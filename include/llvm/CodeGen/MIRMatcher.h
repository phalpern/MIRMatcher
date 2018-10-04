//===-- MIRMatcher.h - MIR pattern matcher ----------------------*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
///
///
/// \file
/// This file implements a pattern matcher for MIR instruction graphs.
///
//===----------------------------------------------------------------------===//

#ifndef INCLUDED_MIRMATCHER_DOT_H
#define INCLUDED_MIRMATCHER_DOT_H

#include "llvm/CodeGen/MachineRegisterInfo.h"

#include <type_traits>

namespace llvm {
namespace mirmatch {

// Standard in C++14 but not in C++11, so we define it here
template <bool cond, class T = void>
using enable_if_t = typename std::enable_if<cond, T>::type;

#if defined(_MSC_VER) && _MSC_VER <= 1900
// Workaround for MS VC 14 (2015) failure to recognize 'return {}' as a constexpr return.
enum no_arg_t { no_arg };
#define CONSTEXPR_DEFAULT_CTOR(classname) constexpr classname(no_arg_t = no_arg) {}
#define EMPTY_CLASS_INITIALIZER no_arg
#else
#define CONSTEXPR_DEFAULT_CTOR(classname) constexpr classname() = default;
#define EMPTY_CLASS_INITIALIZER {}
#endif

namespace internal {

// Base class for a class that implements the interface for a
// *conceptually-homogeneous* typelist, i.e., a list of types that all model
// the same concept. This base class provides access to the size of the type
// list, a predicate to test if a type models the concept for the types in the
// list, the first element of the list, the rest of the list excluding the
// first element, and concatenation of type lists as well as concatenation of
// types into a typelist. The derived class template must be a variadic
// template where the template paramters are a list of types.
template <template <class...> class TypeList, template <class, class...> class Pred,
          class... Types>
struct TypeListBase {
  // Base template is instantiated only when `Types` is empty.
  static constexpr std::size_t size       = 0;
  static constexpr bool        isEmpty    = true;

  template <class Tp> using Predicate = typename Pred<Tp>::type;

  using EmptyListType = TypeList<>;

  static constexpr bool hasValidTypes = true;
};

template <template <class...> class TypeList, template <class, class...> class Pred,
          class Type1, class... Types>
struct TypeListBase<TypeList, Pred, Type1, Types...> {
  // Specialization for at least one parameter
  static constexpr std::size_t size       = 1 + sizeof...(Types);
  static constexpr bool        isEmpty    = false;

  template <class Tp> using Predicate = typename Pred<Tp>::type;

  using EmptyListType = TypeList<>;
  using First         = Type1;
  using Rest          = TypeList<Types...>;

  // Predicate value `hasValidTypes` is true if every type `T` in the list
  // returns a true for `Pred<T>::value`.
  static constexpr bool hasValidTypes =
    Pred<First>::value && Rest::hasValidTypes;
};

// Metafunction to determine if `T` is a type list type.
template <class T, class = void>
struct IsTypeList : std::false_type { };

template <class T>
struct IsTypeList<T, enable_if_t<sizeof(typename T::EmptyListType)>>
  : std::true_type{};

// Metafunction to determine if `T` is an instantiation of `TypeList`.
// This metafunction is more specific than `IsTypeList` because it not only
// checks if `T` is a type list, but checks if it is an instantiation of a
// *specific kind* of type list.
template <template <class...> class TypeList, class T,
          bool = IsTypeList<T>::value>
struct IsTypeListInstantiation : std::false_type {};

template <template <class...> class TypeList, class T>
struct IsTypeListInstantiation<TypeList, T, true>
  : std::is_same<TypeList<>, typename T::EmptyListType>::type {};

// Concatenate one or more type lists. All type lists must be instantiations
// of the specified `TypeList` template.
template <template <class...> class TypeList, class List1, class... Lists>
struct TypeListCatImp; // Primary template is not defined

// Specializaton of `TypeListCatImp` for a single type list.
template <template <class...> class TypeList, class... ElemT>
struct TypeListCatImp<TypeList, TypeList<ElemT...>> {
  using type = TypeList<ElemT...>;
};

// Specializaton of `TypeListCatImp` for two or more type lists.
template <template <class...> class TypeList,
          class... ElemT1, class... ElemT2, class... Others>
struct TypeListCatImp<TypeList, TypeList<ElemT1...>, TypeList<ElemT2...>,
                       Others...> {
  using type =
    typename TypeListCatImp<TypeList,
                             TypeList<ElemT1..., ElemT2...>, Others...>::type;
};

// Helper metafunction transforms `T` to a type list:
//  * If `T` is already an instantiation of `TypeList`, `type` is simply `T`;
//  * otherwise, if the predicate for `TypeList` applies to `T`, `type`
//    is `TypeList<T>`;
//  * otherwise, `type` is not defined (useful for SFINAE).
template <template <class...> class TypeList, class T,
          bool = (IsTypeListInstantiation<TypeList, T>::value ||
                  TypeList<>::template Predicate<T>::value)>
struct AsTypeList
{
  using type = typename
    std::conditional<IsTypeListInstantiation<TypeList, T>::value,
                     T, TypeList<T>>::type;
};

// Specialization for `T` that is not compatible with `TypeList`
template <template <class...> class TypeList, class T>
struct AsTypeList<TypeList, T, false>
{
};

// Concatenate arguments into a type list of the specified kind.
template <template <class...> class TypeList, class... Arg>
using MakeTypeList = typename
  TypeListCatImp<TypeList, TypeList<>,
                  typename AsTypeList<TypeList, Arg>::type...>::type;

} // Close namespace mismatch::internal

// Forward declaration
template <unsigned LocalId = 0>
struct RegisterMatcher;

// Forward declaration
template <class OpMatcher, class DefMatchers, class UseMatchers>
struct InstructionMatcher;

class MatchResult
{
public:

  MatchResult() : m_matched(false) { }
  MatchResult(const MatchResult&) = default;
  MatchResult(MatchResult&&) = default;
  MatchResult& operator=(const MatchResult&) = default;
  MatchResult& operator=(MatchResult&&) = default;

  bool matched() const { return m_matched; }
  operator bool() const { return matched(); }
  bool operator!() const { return ! matched(); }

  MatchResult& setMatched(bool match) { m_matched = match; return *this; }

  ///@brief Associate a register number with a local ID
  ///
  /// Maintains a name-value mapping where "name" is a local ID within this
  /// context and "value" is a register number in the machine function.  Each
  /// ID-reg mapping can be established only once; subsequent attempts to
  /// map the same ID to a different register will fail.  However,
  /// attempting to map an ID more than once to the *same* register will
  /// succeed.  This behavior is important to the matching process, as every
  /// use of a named channel must refer to the same register or else the
  /// match should fail.
  ///
  ///@param LocalId  Local ID (small int) for the register being mapped
  ///@param reg      Name of register within
  bool setRegMapping(unsigned localId, unsigned reg);

  template <unsigned LocalId>
  bool setRegMapping(RegisterMatcher<LocalId>, unsigned reg) {
    return setRegMapping(LocalId, reg);
  }

  unsigned reg(unsigned localId) const;

  template <unsigned LocalId>
  unsigned reg(RegisterMatcher<LocalId>) const { return reg(LocalId); }

  template <class OpMatcher, class DefMatchers, class UseMatchers>
  void setInstrMapping(InstructionMatcher<OpMatcher,
                                          DefMatchers, UseMatchers> matcher,
                       MachineInstr* mi) {
    const void* instrId = matcher.instrId();
    InstrMapEntry entry = { instrId, mi };
    m_instrMap.push_back(entry);
  }

  template <class OpMatcher, class DefMatchers, class UseMatchers>
  MachineInstr* instr(InstructionMatcher<OpMatcher,
                      DefMatchers, UseMatchers> matcher) const {
    return instr(matcher.instrId());
  }

private:
  struct InstrMapEntry {
    const void*   m_key;
    MachineInstr* m_value;
  };

  bool                           m_matched;
  SmallVector<unsigned, 10>      m_regMap;
  SmallVector<InstrMapEntry, 10> m_instrMap;

  MachineInstr* instr(const void* instrId) const;
};

// Compile-time set of up to 64 designated resgisters with LocalIds in the
// range 1 to 64. A LocalId of 0 is a wildcard and is not represented in the
// register set.
template <unsigned long Bits = 0UL>
struct RegisterSet {
  static constexpr unsigned long value = Bits;

  CONSTEXPR_DEFAULT_CTOR(RegisterSet)

  constexpr operator bool()  const { return 0 != value; }
  constexpr bool operator!() const { return 0 == value; }
};

template <unsigned long Bits1, unsigned long Bits2>
constexpr RegisterSet<Bits1 | Bits2> operator|(RegisterSet<Bits1>,
                                               RegisterSet<Bits2>) {
  return EMPTY_CLASS_INITIALIZER;
}

template <unsigned long Bits1, unsigned long Bits2>
constexpr RegisterSet<Bits1 & Bits2> operator&(RegisterSet<Bits1>,
                                               RegisterSet<Bits2>) {
  return EMPTY_CLASS_INITIALIZER;
}

// OperandMatcher Concept:
//
// A class C models this concept if `IsOperandMatcher<C>::value` is true and
// it has the following static member type:
//
//    Registers
//       A specialization of RegisterSet<Bits> indicating the set of registers
//       in the local pattern that are mapped by the operand(s) being
//       matched.
//
// and the following static member function:
//
//    static MachineInstr::const_mop_iterator
//    matchOperand(MatchResult&                     rslt,
//                 MachineInstr::const_mop_iterator op_iter,
//                 MachineInstr::const_mop_iterator op_end);
//       Match the operand against one or more operands in
//       `[op_iter,op_end)` (Most matchers consume only one operand). Return
//       iterator to the last-consumed operand, or `op_end` if match failed.
//       The match `rslt` is updated to reflect attributes of the match,
//       and may be modified to contain useless state on faiure.

// Metafunction to check for types that model the `OperandMatcher` concept.
template <typename OperandMatcher>
struct IsOperandMatcher : std::false_type { };

// Remove const before testing of a type models the `OperandMatcher` concept.
template <typename OperandMatcher>
struct IsOperandMatcher<const OperandMatcher>
  : IsOperandMatcher<OperandMatcher> { };

// PatternMatcher Concept:
//
// A class C models this concept if `IsPatternMatcher<C>::value` is true and
// it has the following static member type:
//
//    Registers
//       A specialization of RegisterSet<Bits> indicating the set of registers
//       in the local pattern that are defined or used by the code being
//       matched.
//
//    SubMatchRange
//
// and the following static member functions:
//
//    static SubMatchRange subMatches(Registers, MRI, result);
//
//    static bool tryMatch(SubMatch, Registers, MRI, result);

//    static bool matchInstr(MatchResult& rslt, MachineInstr* mi);
//        Match the specified `MachineInstr` against the code pattern encoded
//        in this `PatternMatcher`. Return true on a successful match and false
//        otherwise.  The `rslt` object is updated to reflect attributes
//        of the match.  The `rslt` may contain useless state on failure.

// Metafunction to check for types that model the `PatternMatcher` concept.
template <typename PatternMatcher>
struct IsPatternMatcher : std::false_type { };

// Remove const before testing of a type models the `PatternMatcher` concept.
template <typename PatternMatcher>
struct IsPatternMatcher<const PatternMatcher> : IsPatternMatcher<PatternMatcher> { };

// A list of zero or more operand matchers.
template <class... Operands>
struct OperandMatcherList
  : internal::TypeListBase<OperandMatcherList, IsOperandMatcher, Operands...>
{
  using ThisType  = OperandMatcherList;
  using First     = typename ThisType::First;
  using Rest      = typename ThisType::Rest;

  static_assert(ThisType::hasValidTypes,
                "All parameters must be operand matchers");

  static constexpr auto registers = (First::registers | Rest::registers);

  CONSTEXPR_DEFAULT_CTOR(OperandMatcherList)

  template <typename Op, typename Uses>
  constexpr InstructionMatcher<Op, ThisType, Uses>
  operator=(InstructionMatcher<Op, OperandMatcherList<>, Uses>) const
    { return EMPTY_CLASS_INITIALIZER; }

  static bool
  matchOperandRange(MatchResult&                     rslt,
                    MachineInstr::const_mop_iterator iter,
                    MachineInstr::const_mop_iterator opEnd);
};

// A list of one or more operand matchers
template <>
struct OperandMatcherList<>
  : internal::TypeListBase<OperandMatcherList, IsOperandMatcher>
{
  using ThisType = OperandMatcherList;

  static constexpr RegisterSet<> registers{};

  CONSTEXPR_DEFAULT_CTOR(OperandMatcherList)

  static bool
  matchOperandRange(MatchResult&                     rslt,
                    MachineInstr::const_mop_iterator iter,
                    MachineInstr::const_mop_iterator opEnd);
};

// String operand matchers together using commas
template <class Op1, class Op2>
constexpr internal::MakeTypeList<OperandMatcherList, Op1, Op2>
operator,(Op1, Op2) { return EMPTY_CLASS_INITIALIZER; }

// Match any operand
struct AnyOperand_t {
  static constexpr RegisterSet<> registers{};

  CONSTEXPR_DEFAULT_CTOR(AnyOperand_t)

  template <typename Op, typename Uses>
  constexpr InstructionMatcher<Op, OperandMatcherList<AnyOperand_t>, Uses>
  operator=(InstructionMatcher<Op, OperandMatcherList<>, Uses>) const
    { return EMPTY_CLASS_INITIALIZER; }

  static MachineInstr::const_mop_iterator
  matchOperand(MatchResult&                     rslt,
               MachineInstr::const_mop_iterator op_iter,
               MachineInstr::const_mop_iterator op_end)
    { return op_iter; }
};

template <>
struct IsOperandMatcher<AnyOperand_t> : std::true_type { };

constexpr AnyOperand_t AnyOperand{};

template <unsigned LocalId>
struct RegisterMatcher {
  // Match a register operand.  Models the `OperandMatcher` concept. `LocalId`
  // is a small integer in the range 0 to 64 representing a "name" for the
  // register in the current match context. During matching, every instance of
  // the same `LocalId` in the match pattern must refer to the same (physical
  // or virtual) machine register being matched. If `LocalId` is zero, then
  // matches any machine register.

  static_assert(LocalId <= 64, "LocalId must be between 0 and 64");

  static constexpr
  RegisterSet<LocalId ? 1UL << (LocalId ? LocalId - 1 : 0) : 0> registers{};

  static constexpr unsigned localId = LocalId;

  CONSTEXPR_DEFAULT_CTOR(RegisterMatcher)

  template <typename Op, typename Uses>
  constexpr InstructionMatcher<Op, OperandMatcherList<RegisterMatcher>, Uses>
  operator=(InstructionMatcher<Op, OperandMatcherList<>, Uses>) const
    { return EMPTY_CLASS_INITIALIZER; }

  static MachineInstr::const_mop_iterator
  matchOperand(MatchResult&                     rslt,
               MachineInstr::const_mop_iterator op_iter,
               MachineInstr::const_mop_iterator op_end);
};

// Indicate that `RegisterMatcher` models the `OperandMatcher` concept.
template <unsigned LocalId>
struct IsOperandMatcher<RegisterMatcher<LocalId>> : std::true_type { };

constexpr RegisterMatcher<0> AnyRegister{};

// MSVC workaround to force expansion variadic arguments before invoking macro.
#define MIRMATCHER_EXPAND_MACRO(x) x

// Declare a set of register names for use in matching patterns
// The argument list is simply 1 to 20 identifiers, each of which becomes
// a `constexpr` instance of the `RegisterMatcher` template, with the
// ascending local IDs starting at 1.
#define MIRMATCHER_REGS(...)  MIRMATCHER_EXPAND_MACRO(                       \
  MIRMATCHER_REGS_IMP(__VA_ARGS__,(),(),(),(),(),(),(),(),(),(),(),(),(),(), \
                      (),(),(),(),(),()))

// Implementation of `MIRMATCHER_REGS`.  1 to 20 identifiers are passed in
// followed by 20 sets of empty parens.  For each real argument (identifier
// Rx), it expands `MIRMATCHER_COND_DECL_REG` with arguments `(x, Rx,
// MIRMATCHER_2_ARGS Rx)`, where the content of the third argument is
// unimportant. For the remaining arguments (empty parenthesis), it expands
// `MIRMATCHER_COND_DECL_REG` with arguments `(x, (), MIRMATCHER_2_ARGS())`,
// where x is the ordinal position of the argument, and `MIRMATCHER_2_ARGS()`
// is a macro invocation that expands to two arguments whos contents are
// unimportant. Thus, it expands `MIRMATCHER_COND_DECL_REG` with three
// arguments for real registers and four arguments for the empty parens. This
// allows for very different expansions (see below).
#define MIRMATCHER_REGS_IMP(R1, R2, R3, R4, R5, R6, R7, R8, R9, R10, R11,     \
                            R12, R13, R14, R15, R16, R17, R18, R19, R20, ...) \
  MIRMATCHER_COND_DECL_REG(1, R1, MIRMATCHER_2_ARGS R1); \
  MIRMATCHER_COND_DECL_REG(2, R2, MIRMATCHER_2_ARGS R2); \
  MIRMATCHER_COND_DECL_REG(3, R3, MIRMATCHER_2_ARGS R3); \
  MIRMATCHER_COND_DECL_REG(4, R4, MIRMATCHER_2_ARGS R4); \
  MIRMATCHER_COND_DECL_REG(5, R5, MIRMATCHER_2_ARGS R5); \
  MIRMATCHER_COND_DECL_REG(6, R6, MIRMATCHER_2_ARGS R6); \
  MIRMATCHER_COND_DECL_REG(7, R7, MIRMATCHER_2_ARGS R7); \
  MIRMATCHER_COND_DECL_REG(8, R8, MIRMATCHER_2_ARGS R8); \
  MIRMATCHER_COND_DECL_REG(9, R9, MIRMATCHER_2_ARGS R9); \
  MIRMATCHER_COND_DECL_REG(10, R10, MIRMATCHER_2_ARGS R10); \
  MIRMATCHER_COND_DECL_REG(11, R11, MIRMATCHER_2_ARGS R11); \
  MIRMATCHER_COND_DECL_REG(12, R12, MIRMATCHER_2_ARGS R12); \
  MIRMATCHER_COND_DECL_REG(13, R13, MIRMATCHER_2_ARGS R13); \
  MIRMATCHER_COND_DECL_REG(14, R14, MIRMATCHER_2_ARGS R14); \
  MIRMATCHER_COND_DECL_REG(15, R15, MIRMATCHER_2_ARGS R15); \
  MIRMATCHER_COND_DECL_REG(16, R16, MIRMATCHER_2_ARGS R16); \
  MIRMATCHER_COND_DECL_REG(17, R17, MIRMATCHER_2_ARGS R17); \
  MIRMATCHER_COND_DECL_REG(18, R18, MIRMATCHER_2_ARGS R18); \
  MIRMATCHER_COND_DECL_REG(19, R19, MIRMATCHER_2_ARGS R19); \
  MIRMATCHER_COND_DECL_REG(20, R20, MIRMATCHER_2_ARGS R20)

// If invoked with parenthesis, generates two arguments, else not expanded.
#define MIRMATCHER_2_ARGS() 1, 2

// Conditionally expand to either `MIRMATCHER_DECL_REG(N, R)` or to
// `MIRMATCHER_NOP(N, R)` depending on whether it was expanded with three or
// four arguments, respectively.
#define MIRMATCHER_COND_DECL_REG(N, R, ...) MIRMATCHER_EXPAND_MACRO( \
  MIRMATCHER_3RD_ARG(__VA_ARGS__, MIRMATCHER_NOP, MIRMATCHER_DECL_REG, x))(N, R)

// Expand to 3rd argument of argument list.
#define MIRMATCHER_3RD_ARG(x, y, M, ...) M

// Expand to a declaration of an unused function. This definition is
// idempotent, so it can appear any number of times without causing
// a syntax error.
#define MIRMATCHER_NOP(N, R) extern void mireg_nop_function_ignored()

// Expand to the definition of a register matcher with local ID 'N' and name
// 'R'.
#define MIRMATCHER_DECL_REG(N, R) constexpr llvm::mirmatch::RegisterMatcher<N> R{}

template <class T, T val>
struct LiteralMatcher {
  static constexpr T             value = val;
  static constexpr RegisterSet<> registers{};

  CONSTEXPR_DEFAULT_CTOR(LiteralMatcher)

  // Match a literal
  static MachineInstr::const_mop_iterator
  matchOperand(MatchResult&                     rslt,
               MachineInstr::const_mop_iterator op_iter,
               MachineInstr::const_mop_iterator op_end) {
    if (op_iter->isImm() && val == op_iter->getImm())
      return op_iter;  // Match succeeded
    else
      return op_end;   // Match failed
  }
};

template <class T, T v>
struct IsOperandMatcher<LiteralMatcher<T, v>> : std::true_type { };

// Match a literal, regardless of actual value.
struct AnyLiteralMatcher {
  static constexpr RegisterSet<> registers{};

  CONSTEXPR_DEFAULT_CTOR(AnyLiteralMatcher)

  // Match a literal
  static MachineInstr::const_mop_iterator
  matchOperand(MatchResult&                     rslt,
               MachineInstr::const_mop_iterator op_iter,
               MachineInstr::const_mop_iterator op_end) {
    if (op_iter->isImm())
      return op_iter;  // Match succeeded
    else
      return op_end;   // Match failed
  }
};

constexpr AnyLiteralMatcher AnyLiteral{};

template <>
struct IsOperandMatcher<AnyLiteralMatcher> : std::true_type { };

template <class OpMatcher, class DefMatchers, class UseMatchers>
struct InstructionMatcher
{
  // Match an instruction and its operands. `DefMatchers` and `UseMatchers`
  // are type lists of operand matchers corresponding to operand definitions
  // and uses, respectively.

  using Defs      = DefMatchers;
  using Uses      = UseMatchers;

  static constexpr auto registers = (Defs::registers | Uses::registers);

  CONSTEXPR_DEFAULT_CTOR(InstructionMatcher)

  // Match the specified `MachineInstr` against the code opcode and operands
  // encoded in this `InstructionMatcher`. Return true on a successful match
  // and false otherwise.  The match context may be updated to reflect
  // attributes of the match.  The context shall remain unchanged on failure.
  static bool matchInstr(MachineRegisterInfo& MRI,
                         MatchResult& rslt, MachineInstr* mi);

  // Return a pointer that uniquely identifies this instantiation.  It would
  // be nice if we could create a unique ID relative to a specific pattern at
  // compile time, instead.
  static void const* instrId() {
    static const char uniqueness = '\0';
    return &uniqueness;
  }
};

template <class Op, class Defs, class Uses>
struct IsPatternMatcher<InstructionMatcher<Op, Defs, Uses>>
  : std::true_type { };

// Matches a graph of instructions connected through registers.
template <class... PatternMatchers>
struct GraphMatcher
  : internal::TypeListBase<GraphMatcher, IsPatternMatcher, PatternMatchers...>
{
  // Combines zero or more code matchers such that, if ALL match, then this
  // matches.

  using ThisType  = GraphMatcher;
  using Base      =
    internal::TypeListBase<GraphMatcher, IsPatternMatcher, PatternMatchers...>;
  using First     = typename Base::First;
  using Rest      = typename Base::Rest;

  static_assert(ThisType::hasValidTypes,
                "All parameters must be instruction matchers");

  static constexpr auto registers = (First::registers | Rest::registers);

  CONSTEXPR_DEFAULT_CTOR(GraphMatcher)

  // Match the graph if `mi` matches the first instruction listed in the graph
  // and if, by traversing register edges, every other instruction in the
  // graph is matched by a corresponding instruction in the machine IR.
  static bool matchInstr(MachineRegisterInfo& MRI,
                         MatchResult& rslt, MachineInstr* mi);
};

template <>
struct GraphMatcher<>
   : internal::TypeListBase<GraphMatcher, IsPatternMatcher>
{
  // Specialization for an empty graph.

  using ThisType  = GraphMatcher;

  static constexpr RegisterSet<> registers{};

  CONSTEXPR_DEFAULT_CTOR(GraphMatcher)

  static constexpr bool matchInstr(MachineRegisterInfo& MRI,
                                   MatchResult& rslt, MachineInstr* mi)
    { return false; }
};

template <class... PatternMatchers>
struct IsPatternMatcher<GraphMatcher<PatternMatchers...>> : std::true_type { };

// Concatenate instructions into lists
template <class... PatternMatcher>
using ConcatInstr =
  typename internal::MakeTypeList<GraphMatcher, PatternMatcher...>;

// Create a graph matcher from a collection of instruction matchers.  Note
// that the first instruction matcher in the parameter list is special in that
// matching will succeed only if the instruction passed in at runtime matches
// that first paramter. It it is usually most efficient to choose the rarest
// instruction in the graph for the first instruction, so that failing matches
// will fail quickly.
template <class... PatternMatchers>
constexpr GraphMatcher<PatternMatchers...>
graph(PatternMatchers...) { return EMPTY_CLASS_INITIALIZER; }

template <class... PatternMatchers>
struct AlternativeMatcher
  : internal::TypeListBase<AlternativeMatcher, IsPatternMatcher, PatternMatchers...>
{
  // Combines zero or more code matchers such that, if ANY match, then this
  // matches. This primary template is used for a list of alternatives of length
  // greather than zero.

  using ThisType = AlternativeMatcher;
  using Base     =
    internal::TypeListBase<AlternativeMatcher, IsPatternMatcher, PatternMatchers...>;
  using First    = typename Base::First;
  using Rest     = typename Base::Rest;

  static_assert(ThisType::hasValidTypes,
                "All parameters must be instruction matchers");

  static constexpr auto registers = (First::registers & Rest::registers);

  CONSTEXPR_DEFAULT_CTOR(AlternativeMatcher)

  static bool matchInstr(MachineRegisterInfo& MRI,
                         MatchResult& rslt, MachineInstr* mi) {
    return (First::matchInstr(MRI, rslt, mi) ||
            Rest::matchInstr(MRI, rslt, mi));
  }
};

template <>
struct AlternativeMatcher<>
   : internal::TypeListBase<AlternativeMatcher, IsPatternMatcher>
{
  // Combines zero or more code matchers such that, if ANY match, then this
  // matches. This specialization template is used for an empty list of alternatives.

  using ThisType = AlternativeMatcher;

  static constexpr RegisterSet<~0UL> registers{};

  CONSTEXPR_DEFAULT_CTOR(AlternativeMatcher)

  static constexpr bool matchInstr(MachineRegisterInfo& MRI,
                                   MatchResult& rslt, MachineInstr* mi)
    { return false; }
};

template <class PatternMatcher1>
struct AlternativeMatcher<PatternMatcher1> : PatternMatcher1
{
  // Specialization of `AlternativeMatcher` for only one PatternMatcher
  CONSTEXPR_DEFAULT_CTOR(AlternativeMatcher)
};

template <class... PatternMatchers>
struct IsPatternMatcher<AlternativeMatcher<PatternMatchers...>>
  : std::true_type { };

template <class PatternMatcher1, class PatternMatcher2>
constexpr
internal::MakeTypeList<AlternativeMatcher, PatternMatcher1, PatternMatcher2>
operator||(PatternMatcher1, PatternMatcher2) { return EMPTY_CLASS_INITIALIZER; }

// OpMatcher Concept:
//
// A class `C` models this concept if it has the following member functions:
//
//    static constexpr bool match(unsigned v);
//        Returns true if `v` is an opcode matched by this class.
//
//    template <typename... UseMatcher>
//    InstructionMatcher operator()(UseMatcher...) const;
//        Given a list of objects modeling the `OperandMatcher` concept,
//        returns a specialization of the `Instruction` class template.
//
// Note that this concept differs from the `PatternMatcher` interface in that it
// matches (integer) opcodes, not entire instructions or executable blocks.
// `IsOpMatcher<C>::value` should be defined as true for any type `C`
// modeling this concept.

// This class provides two conveniences to creators of `OpMatcher`
// classes: it provides `operator()` to generate an `InstructionMatcher` and
// it declares the `IsOpMatcher` trait. Any class `C` derived from
// `OpMatcherBase<C>` (using the curiously recurring template pattern)
// needs only define the `match` method.
template <class OpMatcher>
struct OpMatcherBase {
  CONSTEXPR_DEFAULT_CTOR(OpMatcherBase)

  // Matcher for a group of zero or more opcodes.
  template <typename... UseMatcher>
  constexpr InstructionMatcher<OpMatcher, OperandMatcherList<>,
                               OperandMatcherList<UseMatcher...>>
  operator()(UseMatcher...) const { return EMPTY_CLASS_INITIALIZER; }
};

// Trait to detect whether `T` is an `OpMatcher`.
template <typename T>
struct IsOpMatcher : std::is_base_of<OpMatcherBase<T>, T> {};

template <typename T>
struct IsOpMatcher<const T> : IsOpMatcher<T>::type {};

template <class... OpMatchers>
struct OpcodeMatcherList :
  OpMatcherBase<OpcodeMatcherList<OpMatchers...>>,
  internal::TypeListBase<OpcodeMatcherList, IsOpMatcher, OpMatchers...>
{
  static_assert(OpcodeMatcherList::hasValidTypes,
                "All parameters must be opcode matchers");

  CONSTEXPR_DEFAULT_CTOR(OpcodeMatcherList)

  static constexpr bool match(unsigned v) {
    return OpcodeMatcherList::First::match(v) ||
      OpcodeMatcherList::Rest::match(v);
  }
};

template <>
struct OpcodeMatcherList<> :
  OpMatcherBase<OpcodeMatcherList<>>,
  internal::TypeListBase<OpcodeMatcherList, IsOpMatcher>
{
	CONSTEXPR_DEFAULT_CTOR(OpcodeMatcherList)

	static constexpr bool match(unsigned v) { return false; }
};

template <class OpMatcher1, class OpMatcher2>
constexpr internal::MakeTypeList<OpcodeMatcherList, OpMatcher1, OpMatcher2>
operator|(OpMatcher1, OpMatcher2) { return EMPTY_CLASS_INITIALIZER; }

// Match a single opcode
template <unsigned Opcode>
struct OpcodeMatcher : OpMatcherBase<OpcodeMatcher<Opcode>>
{
  CONSTEXPR_DEFAULT_CTOR(OpcodeMatcher)

  static constexpr bool match(unsigned v) { return Opcode == v; }
};

// Match a range of opcodes
template <unsigned OpcodeFirst, unsigned OpcodeLast>
struct OpcodeRangeMatcher : OpMatcherBase<OpcodeRangeMatcher<OpcodeFirst, OpcodeLast>>
{
  CONSTEXPR_DEFAULT_CTOR(OpcodeRangeMatcher)

  static constexpr bool match(unsigned v)
    { return OpcodeFirst <= v && v <= OpcodeLast; }
};

// Match a list of opcodes
template <unsigned Opcode1, unsigned... Opcodes>
using OpcodeGroupMatcher = OpcodeMatcherList<OpcodeMatcher<Opcode1>,
                                             OpcodeMatcher<Opcodes>...>;

//////////////// Non-trivial function implementations //////////////////

namespace internal {

struct MatchDef {
  bool operator()(const MachineOperand& mo) const { return mo.isDef(); }
};

struct MatchUse {
  bool operator()(const MachineOperand& mo) const { return mo.isUse(); }
};

} // close namespace internal

template <class... Operands>
bool OperandMatcherList<Operands...>::
matchOperandRange(MatchResult&                     rslt,
                  MachineInstr::const_mop_iterator iter,
                  MachineInstr::const_mop_iterator opEnd)
{
  if (iter == opEnd)
    return false; // Fewer uses or defs than expected

  // Return iterator to last consumed operand, or `opEnd` on failure.
  iter = First::matchOperand(rslt, iter, opEnd);
  if (iter == opEnd)
    return false;

  // Recursively match the remaining operand matchers
  return Rest::matchOperandRange(rslt, ++iter, opEnd);
}

// Specialization for no operand matchers
inline bool OperandMatcherList<>::
matchOperandRange(MatchResult&                     rslt,
                  MachineInstr::const_mop_iterator iter,
                  MachineInstr::const_mop_iterator opEnd)
{
  return iter == opEnd;  // Should be no operands left.
}

template <unsigned LocalId>
MachineInstr::const_mop_iterator
RegisterMatcher<LocalId>::matchOperand(MatchResult&                   rslt,
                                     MachineInstr::const_mop_iterator op_iter,
                                     MachineInstr::const_mop_iterator op_end) {
  if (! op_iter->isReg())
    return op_end;   // FAIL: Not a register operand
  else if (LocalId == 0)
    return op_iter;  // SUCCESS: an unnamed register operand
  else if (rslt.setRegMapping(RegisterMatcher{}, op_iter->getReg()))
    return op_iter;  // SUCCESS: created/confirmed LocalId-register mapping
  else
    return op_end;   // FAIL: LocalId is already mapped to a different reg.
}

template <class OpMatcher, class DefMatchers, class UseMatchers>
bool InstructionMatcher<OpMatcher,
                        DefMatchers,
                        UseMatchers>::matchInstr(MachineRegisterInfo& MRI,
                                                 MatchResult&         rslt,
                                                 MachineInstr*        mi) {

  using ThisPatternMatcher =
    InstructionMatcher<OpMatcher, DefMatchers, UseMatchers>;

  if (! OpMatcher::match(mi->getOpcode()))
    return false;  // FAIL: opcode doesn't match

  // For some reason, there exists `explicit_operands` and `explicit_uses`
  // methods, but not `explicit_defs`. We construct that range manually,
  // here.
  auto operands = mi->explicit_operands();
  auto defs_end = operands.begin() + mi->getNumExplicitDefs();
  if (! DefMatchers::matchOperandRange(rslt, operands.begin(), defs_end))
    return false;  // FAIL: Def operands do not match

  auto uses = mi->explicit_uses();
  if (! UseMatchers::matchOperandRange(rslt, uses.begin(), uses.end()))
    return false;  // FAIL: Use operands do not match

  rslt.setInstrMapping(ThisPatternMatcher{}, mi);
  return true; // MATCHED
}

namespace internal {

// Metafunction to traverse the list of to-be-sorted instructions looking for
// one that defines or uses one of the registers in the register set. Max
// recursion depth is length of `ToBeMatched`.
//
// Parameters:
//   Registers:   A `RegisterSet<>` containing the registers in question
//   ToBeMatched: A `GraphMatcher` of instructions to search
//   FailedMatch: A `GraphMatcher` of instructions known not to define or
//                use one of the registers in `Registers`.
//
// Results:
//   Next:        The first instruction in `ToBeMatched` that defines or uses
//                one of the registers in the register set.
//   Rest:        A concatonation of `FailedMatch` and `ToBeMatched` with
//                `Next` removed.
template <class Registers, class ToBeMatched,
          class FailedMatch = GraphMatcher<>,
          bool = (Registers{} & ToBeMatched::First::registers)>
struct TopoSortFindNext
{
  // Specialization for when `ToBeMatched::First` doesn't use a register in
  // `Registers`.  Add `ToBeMatched::First` to the end of `FailedMatch` and
  // recurse.
  using Recursion =
    TopoSortFindNext<Registers,
                     typename ToBeMatched::Rest,
                     ConcatInstr<FailedMatch, typename ToBeMatched::First>>;

  using Next = typename Recursion::Next;
  using Rest = typename Recursion::Rest;
};

// Specializtion of `TopoSortFindNext` for when `ToBeMatched` begins with an
// instruction that defines or uses a register in `Registers`.
template <class Registers, class ToBeMatched, class FailedMatch>
struct TopoSortFindNext<Registers, ToBeMatched, FailedMatch, true>
{
  using Next = typename ToBeMatched::First;
  using Rest = ConcatInstr<FailedMatch, typename ToBeMatched::Rest>;
};

// Metafunction performs a compile-time topological sort of a list of
// instructions that comprise a graph. Technically, the instructions form a
// cyclic graph and a topo sort is for acyclic graphs. However, we treat the
// graph as acyclic by ignoring the direction of the edges and assuming that
// every edge leads from an earlier node to a later node in the input list.
// Thus, if the list includes instructions (nodes) A and B, in that order, and
// if B is a definition of register rx and A is a use of register rx, we treat
// rx as a forward edge from A to B even though, intuitively, the edge should
// go in the other direction.  All we care about is that consecutive
// instructions in the sorted list share a common register, regardless of the
// direction of data flow through that register.  In fact, they may both be
// definitions or both be uses; for our purposes, they are connected by an
// edge.
//
// The sorting algorithm is similar to a selection sort. However, because we
// don't care about an absolute sort order, each search for the next element in
// the list will terminate on *the first* instruction that meets the criteria,
// rather than *the lowest* instruction in an absolute sort order.
//
// Parameters (both must be specializations of `GraphMatcher<>`):
//   PreSorted:  List of instructions that have already been sorted
//   Unsorted:   List of instructions that have not yet been sorted
//
// Result:
//   type:   A `GraphMatcher` instantiated with the sorted list
template <class Registers, class PreSorted, class Unsorted>
struct TopoSort {
  static_assert(PreSorted::registers & Unsorted::registers,
                "Instruction list must comprise a connected graph");
  using FindNext = TopoSortFindNext<decltype(Registers{} | PreSorted::registers),
                                    Unsorted>;

  using Next = typename FindNext::Next;
  using Rest = typename FindNext::Rest;

  using type = typename TopoSort<Registers, ConcatInstr<PreSorted, Next>, Rest>::type;
};

// Specialization of `TopoSort` for when the entire list has been sorted
// (i.e., the Unsorted list is empty).
template <class Registers, class PreSorted>
struct TopoSort<Registers, PreSorted, GraphMatcher<>> {
  // Recursion stop
  using type = PreSorted;
};

template <class OperandSet, class Registers, int idx = 0,
          bool = OperandSet::First::registers & Registers{}>
struct FirstOperandForRegs {
  using type = typename OperandSet::First;
};

template <class OperandSet, class Registers, int idx>
struct FirstOperandForRegs<OperandSet, Registers, idx, false> :
  FirstOperandForRegs<typename OperandSet::Rest, Registers, idx + 1>
{
};

// Get range of iterators for instructions connected to reg.
// This overload returns definitions of reg only, not uses.
inline iterator_range<MachineRegisterInfo::def_instr_iterator>
instructionsForReg(MachineRegisterInfo& MRI, unsigned reg,
                   std::true_type /* isDef */) {
  return MRI.def_instructions(reg);
}

// Get range of iterators for instructions connected to `reg`.
// This overload returns uses of `reg` only, not definitions.
inline iterator_range<MachineRegisterInfo::use_instr_iterator>
instructionsForReg(MachineRegisterInfo& MRI, unsigned reg,
                   std::false_type /* isDef */) {
  return MRI.use_instructions(reg);
}

template <class InstrList, class MatchedRegisters>
bool recursiveMatch(InstrList, MatchedRegisters mregs, MachineRegisterInfo& MRI,
                    MatchResult& rslt)
{
  /////////// The following computations occur at compile time /////////
  using FirstInstr = typename InstrList::First;
  using Rest       = typename InstrList::Rest;

  // Are we looking for a Def or a Use?  Which one?  If the set of matched
  // registers corresponds to one of the Def operands, then we are looking for
  // a Def, even if another register matches a Use operand.
  using isDef = std::integral_constant<bool,
                                       (FirstInstr::Defs::registers &
                                        MatchedRegisters{})>;

  // Select either the Def operands or the Uses operands
  using OperandSet =
    typename std::conditional<isDef::value,
                              typename FirstInstr::Defs,
                              typename FirstInstr::Uses>::type;

  // Find an operand-matcher that uses to one of the matched registers. If
  // more than one operand-matcher is found, one is chosen (it doesn't matter
  // which).
  using OperandMatcher =
    typename FirstOperandForRegs<OperandSet, MatchedRegisters>::type;

  //////////////// Compile-time computations end here //////////////////////

#if 0
  //////// NEW CODE for GraphMatcher<PatternMatchers...>::iterator::tryMatch //////
  // Iterate over try attempts. When attempt succeeds, recurse. If recursion
  // match fails, try next attempt.
  // For InstructionMatcher, thingsToMatch() simply computes `reg` and returns a
  // range of iterators to instructions connected to it.  The actual token
  // type is not important to this algorithm - it is up to each matcher to
  // define its own. For InstructionMatcher, it's a MachineInstr.
  for (auto& thing : First::thingsToMatch()) {
    MatchResult localRslt = rslt;  // Changes are made to local copy of `rslt`
    if (First::tryMatch(thing, MRI, localRslt) &&
        recursiveMatch(Rest{}, mregs | FirstInstr::registers, MRI, localRslt))
    {
      rslt = std::move(localRslt); // Commit changes to `rslt` on success.
      return true;
    }
    // Changes to `localRslt` are discarded here.
    // Next iteration starts with a fresh copy of `rslt`.
  }
  //////// END NEW CODE /////

#else
  // Get the real register (not the local ID) that was found during earlier
  // matching recurrances.
  unsigned reg = rslt.reg(OperandMatcher{});

  // Iterate over definitions or uses of `reg`, looking for an instruction
  // matched by `FirstInstr`.
  for (MachineInstr& instr : instructionsForReg(MRI, reg, isDef{})) {
    MatchResult localRslt = rslt;  // Changes are made to local copy of `rslt`
    if (FirstInstr::matchInstr(MRI, localRslt, &instr) &&
        recursiveMatch(Rest{}, mregs | FirstInstr::registers, MRI, localRslt))
    {
      rslt = std::move(localRslt); // Commit changes to `rslt` on success.
      return true;
    }
    // Changes to `localRslt` are discarded here.
    // Next iteration starts with a fresh copy of `rslt`.
  }
#endif

  // None of the instructions for `reg` matched. This match failed.
  return false;
}

template <class MatchedRegisters>
bool recursiveMatch(GraphMatcher<>, MatchedRegisters mregs,
                    MachineRegisterInfo& MRI, MatchResult& rslt)
{
  return true;
}

} // Close namespace mirmatch::internal

template <class... PatternMatchers>
bool GraphMatcher<PatternMatchers...>::matchInstr(MachineRegisterInfo& MRI,
                                                  MatchResult&         rslt,
                                                  MachineInstr*        mi)
{
  using namespace internal;

  // Sort the instructions in an order such that the 2nd instruction is
  // connected to the first, the third instruction is connected to one of the
  // first two, etc., so that by matching them in order, we end up traversing
  // the graph.
  using SortedInstr = typename TopoSort<RegisterSet<>,
                                        GraphMatcher<First>, Rest>::type;

  if (! SortedInstr::First::matchInstr(MRI, rslt, mi))
    return false;

  return recursiveMatch(typename SortedInstr::Rest{}, SortedInstr::First::registers,
                        MRI, rslt);
}

template <typename Pattern, class = enable_if_t<IsPatternMatcher<Pattern>::value>>
inline bool match(MatchResult& result, Pattern pat, MachineInstr* mi)
{
  MachineRegisterInfo& MRI = mi->getParent()->getParent()->getRegInfo();
  bool matched = pat.matchInstr(MRI, result, mi);
  result.setMatched(matched);
  return matched;
}

template <typename Pattern, class = enable_if_t<IsPatternMatcher<Pattern>::value>>
inline MatchResult match(Pattern pat, MachineInstr* mi)
{
  MatchResult result;
  match(result, pat, mi);
  return result;
}

} // close namespace mirmatch
} // close namespace llvm

#endif // ! defined(INCLUDED_MIRMATCHER_DOT_H)
