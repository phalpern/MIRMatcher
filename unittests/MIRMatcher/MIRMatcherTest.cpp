//===-- MIRMatcherTest.cpp ----------------------------------*-C++-*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
///
/// \file
/// Test the mirmatcher library.
///
//===----------------------------------------------------------------------===//

#include "llvm/CodeGen/MachineModuleInfo.h"
#include "llvm/CodeGen/MachineRegisterInfo.h"
#include "llvm/CodeGen/MachineInstrBuilder.h"
#include "llvm/Support/TargetRegistry.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/CodeGen/TargetInstrInfo.h"

#include "llvm/CodeGen/MIRMatcher.h"

// Target-specific includes
#include "../lib/Target/X86/X86.h"
#include "../lib/Target/X86/X86RegisterInfo.h"
#include "../lib/Target/X86/X86InstrInfo.h"

#include "gtest/gtest.h"

#include <iostream>
#include <cstring> // std::strncmp
#include <cstdlib> // std::atoi

using namespace llvm;

namespace {

int verbose = 0;

LLVMContext context{};
Module IRModule("TestModule", context);

TargetMachine*     TM      = nullptr;
MachineModuleInfo* MMI     = nullptr;

// Initialize the target machine and create a machine module.
// Note that these are never cleaned up.
bool initTargetMachine() {
  auto TT(Triple::normalize("x86_64"));
  std::string CPU("");
  std::string FS("");

  LLVMInitializeX86TargetInfo();
  LLVMInitializeX86Target();
  LLVMInitializeX86TargetMC();

  std::string Error;
  const Target *TheTarget = TargetRegistry::lookupTarget(TT, Error);
  if (! TheTarget) return false;

  TM = TheTarget->createTargetMachine(TT, CPU, FS, TargetOptions(), None,
                                      CodeModel::Large, CodeGenOpt::Default);
  if (! TM) return false;

  IRModule.setDataLayout(TM->createDataLayout());

  static MachineModuleInfo info(TM);
  info.doInitialization(IRModule);
  MMI = &info;

  return true;
}

// Construct a MachineFunction containing one basic block. Instructions
// are added to the end of the block.
class MIFuncBuilder {

  Function*              m_func;
  MachineFunction&       m_MIFunc;
  TargetInstrInfo const* m_TII;
  MachineBasicBlock*     m_BB;

  const MachineInstrBuilder& addOpnds(const MachineInstrBuilder& builder,
                                      unsigned numdefs)
    { return builder; }

  template <typename... Opnds>
  const MachineInstrBuilder& addOpnds(const MachineInstrBuilder& builder,
                                      unsigned numdefs,
                                      unsigned Reg1, const Opnds&... opnds) {
    if (numdefs > 0)
      return addOpnds(builder.addDef(Reg1), --numdefs, opnds...);
    else
      return addOpnds(builder.addUse(Reg1), 0, opnds...);
  }

  template <typename... Opnds>
  const MachineInstrBuilder& addOpnds(const MachineInstrBuilder& builder,
                                      unsigned numdefs,
                                      const MachineOperand& opnd1,
                                      const Opnds&... opnds) {
    if (numdefs > 0) --numdefs;
    return addOpnds(builder.add(opnd1), numdefs, opnds...);
  }

public:
  MIFuncBuilder(const MIFuncBuilder&) = delete;
  MIFuncBuilder operator=(const MIFuncBuilder&) = delete;

  MIFuncBuilder(const char* name)
    : m_func(cast<Function>(
               IRModule.getOrInsertFunction(name,
                                            Type::getVoidTy(context))))
    , m_MIFunc(MMI->getOrCreateMachineFunction(*m_func))
    , m_TII(m_MIFunc.getSubtarget().getInstrInfo())
    , m_BB(m_MIFunc.CreateMachineBasicBlock()) { }

  ~MIFuncBuilder() {
    MMI->deleteMachineFunctionFor(*m_func);
  }

  Function& func()             const { return *m_func; }
  MachineFunction& MIFunc()    const { return m_MIFunc; }
  TargetInstrInfo const* TII() const { return m_TII; }
  TargetRegisterInfo const* TRI() const {
    return m_MIFunc.getSubtarget().getRegisterInfo(); }
  MachineBasicBlock* BB()      const { return m_BB; }
  MachineRegisterInfo& MRI()   const { return m_MIFunc.getRegInfo(); }
  void dump()                  const { m_BB->dump(); }
  void dump(StringRef s)       const { dbgs() << '\n' << s << '\n'; m_BB->dump(); }

  int createVirtualRegister(const TargetRegisterClass *regClass) {
    return MRI().createVirtualRegister(regClass);
  }

  template <typename... Opnds>
  MachineInstr* addInstr(unsigned OpCode, const Opnds&... opnds) {
    const MCInstrDesc& instrDesc = m_TII->get(OpCode); // Capture1 reference!!
    MachineInstrBuilder bld = BuildMI(m_BB, DebugLoc{}, instrDesc);
    MachineInstr* ret = addOpnds(bld, instrDesc.getNumDefs(), opnds...);
    return ret;
  }
};

// For debugging. `PrintType<T>();` will cause the compilation to fail,
// printing `T` in the error message.
template <class T> struct PrintType;

// Declare opcode matches used for pattern matches
constexpr mirmatch::OpcodeMatcher<X86::PHI>                         PHI{};
constexpr mirmatch::OpcodeMatcher<X86::G_ADD>                       G_ADD{};
constexpr mirmatch::OpcodeMatcher<X86::ADD32ri8>                    ADD32ri8{};
constexpr mirmatch::OpcodeGroupMatcher<X86::MULSDrm, X86::MULSDrr,
                                       X86::MULSSrm, X86::MULSSrr>  MULS{};
constexpr mirmatch::OpcodeGroupMatcher<X86::ADDSDrm, X86::ADDSDrr,
                                       X86::ADDSSrm, X86::ADDSSrr>  ADDS{};

} // Close anonymous namespace

// This tests a simple pattern match, whereby the results of a multiply
// instruction feed into an add instruction. (In real life, detecting this
// pattern would allow the compiler to replace both instructions with a single
// FMA instruction.)
TEST(MIRMatcher, FMAPattern) {
  using MO = MachineOperand;

  // Construct function using X86 opcodes
  MIFuncBuilder builder("FMAPattern");

  const unsigned p    = builder.createVirtualRegister(&X86::GR64RegClass);
  const unsigned a    = builder.createVirtualRegister(&X86::FR64RegClass);
  const unsigned x    = builder.createVirtualRegister(&X86::FR64RegClass);
  const unsigned y    = builder.createVirtualRegister(&X86::FR64RegClass);
  const unsigned ax   = builder.createVirtualRegister(&X86::FR64RegClass);
  const unsigned axpy = builder.createVirtualRegister(&X86::FR64RegClass);

  // The following copies are scaffolding that appear in real code. They are
  // not technically neccessary for this test, but it is good to be both
  // realistic and to make sure that the pattern matcher is robust in the
  // presence of irrelevent instructions.
  MachineInstr* cpy = builder.addInstr(X86::COPY, y, X86::XMM2);
  MachineInstr* cpx = builder.addInstr(X86::COPY, x, X86::XMM1);
  MachineInstr* cpa = builder.addInstr(X86::COPY, a, X86::XMM0);
  MachineInstr* cpp = builder.addInstr(X86::COPY, p, X86::RDI);

  // Here is the heart of the code we are matching. It consists of a multiply
  // followed by an irrelevent instruction (which happens to be an add),
  // followed by an add that takes one of its inputs from the multiply.
  MachineInstr* mul = builder.addInstr(X86::MULSDrr, ax, a, x);
  MachineInstr* inc = builder.addInstr(X86::ADD32mi8, p,
                                       MO::CreateImm(1), X86::NoRegister,
                                       MO::CreateImm(0), X86::NoRegister,
                                       MO::CreateImm(1));
  MachineInstr* add = builder.addInstr(X86::ADDSDrr, axpy, ax, y);

  // The following return sequence appears in real code. It are not
  // technically neccessary for this test, but it is good to be both realistic
  // and to make sure that the pattern matcher is robust in the presence of
  // irrelevent instructions.
  MachineInstr* cpr = builder.addInstr(X86::COPY, X86::XMM0, axpy);
  MachineInstr* ret = builder.addInstr(X86::RET, MO::CreateImm(0), X86::XMM0);

  (void) cpy;
  (void) cpx;
  (void) cpa;
  (void) cpp;
  (void) mul;
  (void) inc;
  (void) add;
  (void) cpr;
  (void) ret;

  if (verbose)
    builder.dump("Before FMA Transformation");

  /////////// Find the match the hard way: without MIRMatcher ///////////////
  bool hardwayMatch = [=,&builder](MachineInstr* pi){
    MachineRegisterInfo& MRI = builder.MRI();

    // Variables to capture match results.
    unsigned rX, rY, rAX, rAXPY;  // Registers
    const MachineInstr *iADD, *iMUL;    // Instruction
    if (pi->getOpcode() == X86::MULSDrm || pi->getOpcode() == X86::MULSDrr ||
        pi->getOpcode() == X86::MULSSrm || pi->getOpcode() == X86::MULSSrr) {
      iMUL = pi;  // Found the multiply instruction
      if (! iMUL->getOperand(0).isReg() || ! iMUL->getOperand(2).isReg())
        return false;
      auto& oA = iMUL->getOperand(1);
      rX  = iMUL->getOperand(2).getReg(); rAX = iMUL->getOperand(0).getReg();

      // Find add instruction
      for (const MachineInstr& instr : MRI.use_instructions(rAX)) {
        if (instr.getOpcode() == X86::ADDSDrm || instr.getOpcode() == X86::ADDSDrr ||
            instr.getOpcode() == X86::ADDSSrm || instr.getOpcode() == X86::ADDSSrr) {
          if (! instr.getOperand(0).isReg() ||
              ! instr.getOperand(1).isReg() || ! instr.getOperand(2).isReg())
            continue;  // Backtrack and check next instruction
          if (instr.getOperand(1).getReg() != rAX)
            continue;  // Backtrack and check next instruction

          // Found add instruction. Success! Set match results.
          rY    = instr.getOperand(2).getReg();
          rAXPY = instr.getOperand(0).getReg();
          iADD  = &instr;

          // Check that everything is as expected.
          (void) oA;
          EXPECT_EQ(rX, x);
          EXPECT_EQ(rY, y);
          EXPECT_EQ(rAX, ax);
          EXPECT_EQ(rAXPY, axpy);
          EXPECT_EQ(iMUL, mul);
          EXPECT_EQ(iADD, add);

          return true; // Found match
        }
      }
    }
    return false; // Match failed
  }(mul);
  EXPECT_TRUE(hardwayMatch);

  /////////// Find the match the easy way: with MIRMatcher ///////////////
  using namespace mirmatch;
  mirmatch::MatchResult result;

  MIRMATCHER_REGS(REG_X, REG_Y, REG_AX, REG_AXPY);

  // Match pattern 'y = a*x + y'
  // Note that the output of the multiply (REG_AX) is used as input to the add.
  constexpr auto fmapattern =
    mirmatch::graph(REG_AX   = MULS(AnyOperand, REG_X),
                    REG_AXPY = ADDS(REG_AX, REG_Y));

  bool matched = mirmatch::match(result, fmapattern, mul);
  ASSERT_TRUE(matched);
  ASSERT_TRUE(result);
  EXPECT_EQ(result.reg(REG_X), x);
  EXPECT_EQ(result.reg(REG_Y), y);
  EXPECT_EQ(result.reg(REG_AX), ax);
  EXPECT_EQ(result.reg(REG_AXPY), axpy);

  EXPECT_EQ(mul, result.instr(REG_AX   = MULS(AnyOperand, REG_X) ));
  EXPECT_EQ(add, result.instr(REG_AXPY = ADDS(REG_AX, REG_Y)     ));

  // Perform FMA transformation
  {
    TargetInstrInfo const* TII = builder.TII();
    MachineRegisterInfo& MRI = builder.MRI();

    if (MRI.hasOneUse(result.reg(REG_AX))) {
      MachineInstr* mul = result.instr(REG_AX   = MULS(AnyOperand, REG_X) );
      MachineInstr* add = result.instr(REG_AXPY = ADDS(REG_AX, REG_Y)     );
      MachineBasicBlock& BB = *add->getParent();
      BuildMI(BB, add, mul->getDebugLoc(), TII->get(X86::VFMADD213SDr))
        .addDef(result.reg(REG_AXPY))
        .addUse(result.reg(REG_X))
        .add   (mul->getOperand(1))
        .addUse(result.reg(REG_Y));
      mul->eraseFromParent();
      add->eraseFromParent();

      if (verbose)
        builder.dump("After FMA Transformation");
    }
  }
}

// Simply test that if pattern is not found, then pattern match will fail.
TEST(Intel_MIRMatcher, FailMatch) {
  using MO = MachineOperand;

  // Construct function using X86 opcodes.
  // Function does not match pattern because the two add instructions are not
  // related to each other.
  MIFuncBuilder builder("FailMatch");
  const unsigned r0 = builder.createVirtualRegister(&X86::GR32RegClass);
  const unsigned v0 = builder.createVirtualRegister(&X86::GR32RegClass);
  const unsigned r1 = builder.createVirtualRegister(&X86::GR32RegClass);
  const unsigned v1 = builder.createVirtualRegister(&X86::GR32RegClass);
  MachineInstr* add0 = builder.addInstr(X86::G_ADD, r0, v0, MO::CreateImm(0));
  MachineInstr* add1 = builder.addInstr(X86::G_ADD, r1, v1, MO::CreateImm(4));
  (void) add1;

  if (verbose)
    builder.dump("Add + Add");

  using namespace mirmatch;

  MIRMATCHER_REGS(REG_AB);

  // Match pattern 'r = a + b + c'
  // Note that the output of the multiply (REG_AX) is used as input to the add.
  constexpr auto pat =
    mirmatch::graph(REG_AB      = G_ADD(AnyOperand, AnyOperand),
                    AnyRegister = G_ADD(REG_AB, AnyOperand));

  auto result = mirmatch::match(pat, add0);
  ASSERT_FALSE(result);  // Won't match
}

// Find induction variables. This test demonstrates the ability to match
// cycles. An induction variable is a value that has an initial value that
// flows into a loop and is incremented within the loop body.
TEST(MIRMatcher, FindInductionVar) {
  using MO = MachineOperand;

  // Construct function using X86 opcodes.
  // Code corresponds to the loop body and increments of this C code:
  //
  // void InductionVars(int s, int n)
  // {
  //   int a = s;
  //   for (int b = 0; b < n; ++b, a += 2)
  //     foo(a, b);
  // }

  MIFuncBuilder builder("InductionVars");

  const unsigned a      = builder.createVirtualRegister(&X86::GR32RegClass);
  const unsigned a_init = builder.createVirtualRegister(&X86::GR32RegClass);
  const unsigned a_incr = builder.createVirtualRegister(&X86::GR32RegClass);
  const unsigned b      = builder.createVirtualRegister(&X86::GR32RegClass);
  const unsigned b_init = builder.createVirtualRegister(&X86::GR32RegClass);
  const unsigned b_incr = builder.createVirtualRegister(&X86::GR32RegClass);

  builder.addInstr(X86::COPY, a, X86::ESI);
  builder.addInstr(X86::COPY, b, MO::CreateImm(0));
  MachineInstr* phi_a = builder.addInstr(X86::PHI, a, a_init, a_incr);
  MachineInstr* phi_b = builder.addInstr(X86::PHI, b, b_init, b_incr);
  builder.addInstr(X86::ADJCALLSTACKDOWN64,
                   MO::CreateImm(0), MO::CreateImm(0), MO::CreateImm(0));
  builder.addInstr(X86::COPY, X86::EDI, b);
  builder.addInstr(X86::COPY, X86::ESI, a);
  builder.addInstr(X86::CALL64pcrel32, MO::CreateES("foo"),
                   MO::CreateRegMask(
                     builder.TRI()->getCallPreservedMask(builder.MIFunc(),
                                                         CallingConv::C)));
  builder.addInstr(X86::ADJCALLSTACKUP64,
                   MO::CreateImm(0), MO::CreateImm(0));
  MachineInstr* inc_a = builder.addInstr(X86::ADD32ri8, a_incr,
                                         a, MO::CreateImm(1));
  MachineInstr* inc_b = builder.addInstr(X86::ADD32ri8, b_incr,
                                         b, MO::CreateImm(2));

  if (verbose)
    builder.dump("Loop");

  using namespace mirmatch;

  MIRMATCHER_REGS(IVAR, IVAR_INIT, IVAR_INCR);

  // Match pattern values that are incremented from within a loop.
  // The pattern contains a cycle whereby the induction variable is indirectly
  // dependent on itself (flowing from iteration to iteration).
  constexpr auto ivpattern =
    mirmatch::graph(IVAR      = PHI(IVAR_INIT, IVAR_INCR),
                    IVAR_INCR = ADD32ri8(IVAR, AnyLiteral));

  bool matched_a = false, matched_b = false;

  MachineBasicBlock* BB = builder.BB();
  for (auto &Instr : *BB) {
    auto result = mirmatch::match(ivpattern, &Instr);
    if (! result)
      continue;

    if (verbose) {
      auto incrInstr = result.instr(IVAR_INCR = ADD32ri8(IVAR, AnyLiteral));
      auto increment = incrInstr->getOperand(2).getImm();
      std::cout << "Found induction variable " << result.reg(IVAR)
                << ", initialization reg " <<  result.reg(IVAR_INIT)
                << ", increment " << increment << std::endl;
    }

    if (&Instr == phi_a) {
      matched_a = true;

      EXPECT_EQ(result.reg(IVAR), a);
      EXPECT_EQ(result.reg(IVAR_INIT), a_init);
      EXPECT_EQ(result.reg(IVAR_INCR), a_incr);

      EXPECT_EQ(phi_a, result.instr(IVAR      = PHI(IVAR_INIT, IVAR_INCR)));
      EXPECT_EQ(inc_a, result.instr(IVAR_INCR = ADD32ri8(IVAR, AnyLiteral)));
    }
    else if (&Instr == phi_b) {
      matched_b = true;

      EXPECT_EQ(result.reg(IVAR), b);
      EXPECT_EQ(result.reg(IVAR_INIT), b_init);
      EXPECT_EQ(result.reg(IVAR_INCR), b_incr);

      EXPECT_EQ(phi_b, result.instr(IVAR      = PHI(IVAR_INIT, IVAR_INCR)));
      EXPECT_EQ(inc_b, result.instr(IVAR_INCR = ADD32ri8(IVAR, AnyLiteral)));
    }
    else
      EXPECT_TRUE(false && "Unexpected match");
  }

  EXPECT_TRUE(matched_a);
  EXPECT_TRUE(matched_b);
}

int main(int argc, char *argv[]) {

  ::testing::InitGoogleTest(&argc, argv);

  for (int i = 0; i < argc; ++i) {
    if (std::strcmp(argv[i], "-verbose") == 0)
      ++verbose;
  }

  if (initTargetMachine())
    return RUN_ALL_TESTS();
  else
    std::cerr << "FAILED to initialize target machine" << std::endl;
}

/* End MMatcher2.cpp */
