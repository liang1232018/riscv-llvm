#ifndef __MINFAT_H
#define __MINFAT_H

#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>

#include <assert.h>

#define MINFAT_TAG_MASK             (0xFC00000000000000)
#define MINFAT_PTR_MASK             (0x03FFFFFFFFFFFFFF)
#define MINFAT_BASE_SIZE            6
#define MINFAT_TAG_OFFSET           58

#define MINFAT_CONST      __attribute__((__const__))
#define MINFAT_NORETURN   __attribute__((__noreturn__))
#define MINFAT_MALLOC     __attribute__((__malloc__))
#define MINFAT_INLINE     __attribute__((__always_inline__))

static inline MINFAT_CONST MINFAT_INLINE size_t minfat_base_rt(const void *_ptr)
{
    size_t size_base = MINFAT_TAG_MASK & (size_t)_ptr;
    size_base = ~size_base >> MINFAT_TAG_OFFSET;
    if(size_base == 0) 
        return 0xFFFFFFFFFFFFFFFF;
    size_t mask = 0xFFFFFFFFFFFFFFFF << size_base;
    return (mask & (size_t)_ptr);
}

static inline MINFAT_CONST MINFAT_INLINE size_t minfat_size(const void *_ptr)
{
    size_t size_base = MINFAT_TAG_MASK & (size_t)_ptr;
    size_base = ~size_base >> MINFAT_TAG_OFFSET;
    size_t size = 1ull << size_base;
    return size;
}

static inline MINFAT_CONST MINFAT_INLINE size_t minfat_buffer_size(
    const void *_ptr)
{
    size_t size = minfat_size(_ptr);
    size_t base = minfat_base_rt(_ptr);
    // size_t masked_ptr = (size_t)_ptr & MINFAT_PTR_MASK;
    return (size - ((size_t)_ptr - base));
    // return minfat_size(_ptr) -
    //     ( ((size_t)_ptr & MINFAT_PTR_MASK) - minfat_base_rt(_ptr) );
}

static size_t clz(size_t value) {
    size_t res = 1;
    
    if (value == 0) {
        res = 64;
    }
    else {
        if ((value >> 32) == 0) { res += 32; value = value << 32; }
        if ((value >> 48) == 0) { res += 16; value = value << 16; }
        if ((value >> 56) == 0) { res += 8; value = value << 8; }
        if ((value >> 60) == 0) { res += 4; value = value << 4; }
        if ((value >> 62) == 0) { res += 2; value = value << 2; }
        res = res - (value >> 63);
    }
    return res;
}

#endif      // __SMA_H