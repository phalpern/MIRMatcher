set(LLVM_LINK_COMPONENTS
  ${LLVM_TARGETS_TO_BUILD}
  CodeGen
  Core
  MC
  Support
  Target
  )

if(";${LLVM_TARGETS_TO_BUILD};" MATCHES ";X86;")
include_directories(
  ${CMAKE_BINARY_DIR}/lib/Target/X86/
)

  add_llvm_unittest(MIRMatcherTests
    MIRMatcherTest.cpp
    )
endif()
