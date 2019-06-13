set(LLVM_LINK_COMPONENTS
  Support
  )

add_clang_executable(clang-peregrine
    ClangPeregrine.cpp
    )

target_link_libraries(clang-peregrine
    PRIVATE
    clangAST
    clangBasic
    clangDriver
    clangFormat
    clangLex
    clangParse
    clangSema
    clangFrontend
    clangTooling
    clangToolingCore
    clangRewrite
    clangRewriteFrontend
)

# if(UNIX)
#   set(CLANGXX_LINK_OR_COPY create_symlink)
# else()
#   set(CLANGXX_LINK_OR_COPY copy)
# endif()

install(TARGETS clang-peregrine
  RUNTIME DESTINATION bin)
