add_compiler_rt_component(sma)

set(SMA_SOURCE minfat.c minfat_malloc.c)

include_directories(..)

set(SMA_CFLAGS -std=gnu99 -I. -O2)

add_compiler_rt_runtime(clang_rt.sma
        STATIC
        ARCHS x86_64 aarch64 riscv64
        SOURCES ${SMA_SOURCE}
        CFLAGS ${SMA_CFLAGS}
        PARENT_TARGET sma)

add_sanitizer_rt_symbols(clang_rt.sma)

add_dependencies(compiler-rt sma)
