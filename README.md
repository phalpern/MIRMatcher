# MIRMatcher

## Introduction

This library is pattern matcher for LLVM Machine Intermediate Representation
(Machine IR or MIR).  MIRMatcher is useful within optimization passes that run
after instruction selection, i.e., for finding instruction patterns that can
be replaced with more efficient instructions.

MIRMatcher has the following attributes:

 * It has an embedded domain-specific language (EDSL) for specifying the
   pattern to be matched. This EDSL has a Syntax that resembles an LLVM dump
   of Machine IR.

 * It supports matching patterns that contain cycles.

 * The pattern-matching machinery is constructed when the LLVM pass is
   compiled, so no interpretation of the pattern takes place at run time.

 * It uses advanced C++ metaprogramming.

MIRMatcher and the C++ techniques that make it work are described in Pablo
Halpern's CppCon 2018 talk, _Using Compile-time Code Generation to build an
LLVM IR Pattern Matcher_. This talk will be available on YouTube sometime in
October or November, 2018. Search YouTube for "Pablo Halpern CppCon 2018". The
slides for this talk are in the top-level directory of this repository.

**This code is still in early development. It has already drifted a bit from
what was presented at CppCon (mostly some class names were changed). At this
point, it should be considered a toy, for educational purposes. Eventually,
Pablo hopes to upstream the component into the LLVM mainline.**

## Installation

Use this library by merging this repository with a fork of the LLVM
repository. Alternatively, simply copy the files into the corresponding
subdirectories of the LLVM source tree.

In order to build the MIRMatcherTests target, you will need to add the
following lines to the `unittests/CMakeLists.txt` file:

    if(";${LLVM_TARGETS_TO_BUILD};" MATCHES ";X86;")
    add_subdirectory(MIRMatcher)
    endif()

The unit test will not build unless one of the targets being built is X86
because x86_64 instructions are used in the examples.

## Usage Example

This example searches for a **multiply** instruction whose output feeds into
and **add** instruction (in x86_64). The idea is that an optimization
pass can replace this pattern with a **fused multiply-add (FMA)**
instruction. (In a real LLVM compiler, this step is performed at instruction
selection, but not all such optimizations can be done that early.) This
example is extracted from the unit test and is described more completely in
the accompanying PowerPoint slides from Pablo's CppCon 2018 talk.

```C++
  using namespace mirmatch;

  constexpr OpcodeGroupMatcher<X86::MULSDrm, X86::MULSDrr,
                               X86::MULSSrm, X86::MULSSrr>  MULS{};
  constexpr OpcodeGroupMatcher<X86::ADDSDrm, X86::ADDSDrr,
                               X86::ADDSSrm, X86::ADDSSrr>  ADDS{};

  MIRMATCHER_REGS(REG_X, REG_Y, REG_AX, REG_AXPY);

  // Match pattern 'y = a*x + y'
  // Note that the output of the multiply (REG_AX) is used as input to the add.
  constexpr auto fmapattern =
    mirmatch::graph(REG_AX   = MULS(AnyOperand, REG_X),
                    REG_AXPY = ADDS(REG_AX, REG_Y));

  mirmatch::MatchResult result;
  bool matched = mirmatch::match(result, fmapattern, mul);
  ASSERT_TRUE(matched);
  ASSERT_TRUE(result);
  EXPECT_EQ(result.reg(REG_X), x);
  EXPECT_EQ(result.reg(REG_Y), y);
  EXPECT_EQ(result.reg(REG_AX), ax);
  EXPECT_EQ(result.reg(REG_AXPY), axpy);

  EXPECT_EQ(mul, result.instr(REG_AX   = MULS(AnyOperand, REG_X) ));
  EXPECT_EQ(add, result.instr(REG_AXPY = ADDS(REG_AX, REG_Y)     ));
```
  
## Ever-so-brief user manual:

All classes and functions are in the namespace `llvm::mirmatch`.

### Class `MatchResult`

An object of class `MatchResult` holds the result of an attempted pattern
match at runtime.

```C++
  class MatchResult
  {
  public:

    // Return true if match was found
    bool matched() const;
    operator bool() const;

    // Return false if match was found
    bool operator!() const;

    // Return the register that matched register-name
    template <register-id>
      unsigned reg(register-name) const;

    // Return the instruction that matched the instruction expression
    template <instruction-type>
      MachineInstr* instr(instruction-expression) const;
  };
```

### Class templates `OpcodeMatcher`, `OpcodeRangeMatcher`, and `OpcodeGroupMatcher`

An object instantiated from one of these templates is used to construct an
instruction pattern within a match pattern. The instruction pattern will match
an instruction that matches a single opcode, a range of opcodes, or an
arbitrary group of opcodes, respectively.

```C++
  template <unsigned Opcode> class OpcodeMatcher;
  template <unsigned OpcodeFirst, unsigned OpcodeLast> class OpcodeRangeMatcher;
  template <unsigned Opcode1, unsigned... Opcodes> class OpcodeGroupMatcher;
```

### Macro `MIR_MATCHER_REGS(r1, r2, ...)`

Declares one or more register names that can be used to match registers in a
code pattern. These names can be used after a successful match is found to
retrieve the values of the actual registers that were matched.

### Function `mirmatch::graph(instructions...)`

Creates a match pattern from a list of instructions.  Each instruction is of
the form

_output-registers_ `=` _opcode_ `(` _input-operands_ `)`

where _output-registers_ is a comma-separated list of one or more of the names
defined with the `MIR_MATCHER_REGS` macro or `AnyRegister`. If more than one
output register is specified (rare), the list must be enclosed in
parenthesis. If there are no output registers, then the assignment operator is
omitted from the pattern. _opcode_ is an object of type obtained from
instantiating the `OpcodeMatcher`, `OpcodeRangeMatcher`, or
`OpcodeGroupMatcher` templates.  _input-operands_ is a list of zero or more
input operands. Each input operands can be a named register defined with
`MIR_MATCHER_REGS`, `AnyRegister`, an object that is an instantiation of
`LiteralMatcher<Type, Value>`, or `AnyLiteral`.  As implied by the name, an
object of type `LiteralMatcher<Type, Value>` matches an integral literal
operand with the specified value.

The instructions that constitute a graph match must form a connected dataflow
graph. That is, at least one operand from every instruction must be a register
used by at least one of the other instructions such that the entire set forms
a single graph. Cycles are allowed. (The ability to support cycles in the
pattern is one of the things that distinguishes MIRMatcher from other matching
libraries.)

### Function `match`

```C++
  bool match(MatchResult& result, Pattern pat, MachineInstr* mi);
  MatchResult match(Pattern pat, MachineInstr* mi);
```

Given a pattern and a pointer to an instruction, these functions find a match
if the instruction is the first instruction in the pattern graph. The first
variant returns true on match and false otherwise. The second variant returns
the result object, which is is convertible to bool (true on success). In both
cases, the matched (named) registers and instructions are stored in the the
result object, where they can be retrieved using the `reg()` and `instr()`
member functions.

## Future improvements

 * Better Documentation.
 * Extend capabilities to the LLVM (portable) IR, not just the machine IR.
 * Support composition of subpatterns into patterns.
 * Alternatives (match this or that)
 * Stateful (but still small and readonly) patterns

