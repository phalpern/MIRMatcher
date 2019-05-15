//===-- MIRMatcher.cpp - MIR pattern matcher --------------------*- C++ -*-===//
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

#include "llvm/CodeGen/MIRMatcher.h"

namespace llvm {

bool mirmatch::MatchResult::setRegMapping(unsigned localId, unsigned reg)
{
  if (0 == localId)
    return true;  // localId of zero matches any register. Do not map.

  unsigned index = localId - 1;
  if (m_regMap.size() <= index)
    m_regMap.resize(index + 1, 0);

  if (0 == m_regMap[index]) {
    m_regMap[index] = reg;
    return true;
  } else
    return m_regMap[index] == reg;
}

unsigned mirmatch::MatchResult::reg(unsigned localId) const {
  if (0 == localId)
    return 0;

  unsigned index = localId - 1;
  if (index < m_regMap.size())
    return m_regMap[index];
  else
    return 0;
}

llvm::MachineInstr* mirmatch::MatchResult::instr(const void* instrId) const {
  for (auto& entry : m_instrMap)
    if (entry.m_key == instrId)
      return entry.m_value;
  return nullptr;
}

} // Close namespace llvm

// End MIRMatcher.cpp
