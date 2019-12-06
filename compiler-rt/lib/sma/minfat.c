#include <errno.h>
#include <string.h>

#include <signal.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#include "minfat.h"

extern MINFAT_CONST void minfat_ptr_debug(void *ptr)
{
    fprintf(stderr, " [minfat_ptr_debug]: %p\n", ptr);
    return;
}

extern MINFAT_CONST void minfat_baseptr_debug(void *ptr, void *baseptr)
{
    // if ((size_t)baseptr > (size_t)ptr) {
    //     fprintf(stderr, "[minfat_baseptr_debug]: wierd....\n");
    //     fprintf(stderr, "  ptr: %p, base: %p\n", ptr, baseptr);
    // }
    if (baseptr != NULL)
        fprintf(stderr, "baseptr(not memeory allocation): %p\n", baseptr);
    return;
}

extern MINFAT_CONST void minfat_baseptr_debug2(void *baseptr)
{
    // if ((size_t)baseptr > (size_t)ptr) {
    //     fprintf(stderr, "[minfat_baseptr_debug]: wierd....\n");
    //     fprintf(stderr, "  ptr: %p, base: %p\n", ptr, baseptr);
    // }
    if (baseptr != NULL)
        fprintf(stderr, "baseptr(memeory allocation): %p\n", baseptr);
    return;
}

extern MINFAT_CONST void minfat_ptr_oob_message(void *ptr)
{
    printf(" [minfat_ptr_oob_message]: %p, out of bounds!\n", ptr);
    return;
}

// // extern inline _MINFAT_CONST _MINFAT_INLINE void* minfat_base(const void *_ptr)
// extern _MINFAT_CONST void* minfat_base(const void *_ptr)
// {
    
// }

MINFAT_INLINE extern inline MINFAT_CONST size_t minfat_stack_allocsize(size_t ori_size)
{
    return (1ull << (64 - clz(ori_size)));
}


MINFAT_INLINE extern inline MINFAT_CONST void* minfat_sp_align(void *ptr, size_t size)
{
    size_t mask = 0xFFFFFFFFFFFFFFFF & size;
    size_t aligned_ptr = (size_t)ptr & mask;
    return (void*)aligned_ptr;
}

MINFAT_INLINE extern inline MINFAT_CONST void* minfat_pointer_package(void *ptr, size_t size)
{
    size_t base = 63 - clz(size);
    size_t tag;

    if ((1ull << base) ^ size)
        tag = base + 1;
    else
        tag = base;

    size_t invert_tag = ~tag & 0x3F;
    invert_tag = invert_tag << MINFAT_TAG_OFFSET;

    void *ret = (void*)((size_t)ptr | invert_tag);
    // void *ret = ptr;

    // printf(" [minfat_pointer_package]: DEBUG INFO\n");
    // printf("  ptr:      %p\n", ptr);
    // printf("  ori_size: %lu\n", size);
    // printf("  tag:      0x%lx\n", tag);
    // printf("  ret:      %p\n\n", ret);
    
    return ret;
}

#define OOB_ERROR_DEBUG
MINFAT_INLINE extern inline MINFAT_CONST void* minfat_oob_check_rt(void *ptr, void *base, size_t access_size)
{
    // fprintf(stderr, "base: %p, ptr: %p\n", base, ptr);

    // ptr may be tagged, base is sure to have tag
    size_t tag = (size_t)base & MINFAT_TAG_MASK;
    size_t size_base = ((~tag) >> MINFAT_TAG_OFFSET) & 0x3F;
    size_t size = 1ull << size_base;
    
    // size_t masked_base = (size_t)base & MINFAT_PTR_MASK;
    size_t masked_ptr = (size_t)ptr & MINFAT_PTR_MASK;
    size_t tagged_ptr = masked_ptr | tag;

    size_t bound = (size_t)base + size;
    size_t access_bound = bound - access_size;

    void *ret = (void*)tagged_ptr;

#ifdef OOB_ERROR_DEBUG
    bool oob_error = false;
    if (tagged_ptr < (size_t)base) {
        // ret = base;
        oob_error = true;

        // char a = *(char*)ptr;
        // fprintf(stderr, "  content(byte): 0x%x\n", a);
    }
    else if (tagged_ptr > access_bound) {
        // ret = (void*)access_bound;
        oob_error = true;
    }

    if (oob_error) {
        fprintf(stderr, "[minfat_oob_check]: OOB ERROR!\n");
        fprintf(stderr, "  ptr:          %p\n", ptr);
        fprintf(stderr, "  tagged_ptr:   0x%lx\n", tagged_ptr);
        fprintf(stderr, "  base:         %p\n", base);
        fprintf(stderr, "  size_base:    %lu\n", size_base);
        fprintf(stderr, "  size:         %lu\n", size);
        fprintf(stderr, "  access_size:  %lu\n", access_size);
        fprintf(stderr, "  access_bound: 0x%lx\n", access_bound);
        fprintf(stderr, "  bound:        0x%lx\n", bound);
        fprintf(stderr, "  ret:          %p\n", ret);
        char a = *(char*)masked_ptr;
        fprintf(stderr, "  content:      0x%lx\n", a);
        minfat_free(ptr);
        abort();
    }
#else
    ret = (tagged_ptr < (size_t)base) ? base : ret;
    ret = (tagged_ptr > access_bound) ? (void*)access_bound : ret;
#endif

    return ret;
}

// extern void* ptr_cmp(void *ptr, void *base, size_t access_size, void *ir) {
//     void *c = minfat_oob_check_rt(ptr, base, access_size);
//     if (ir == c) 
//         return ir;
//     else {
//         fprintf(stderr, "[ptr_cmp]: ir: 0x%p, c: 0x%p\n", ir, c);
//         return c;
//     }
// }

extern void* minfat_base_debug(void *ptr)
{
    size_t invert_tag = (size_t)ptr & MINFAT_TAG_MASK;
    size_t tag = ~invert_tag;
    tag = tag >> MINFAT_TAG_OFFSET;
    size_t mask = (size_t)0xFFFFFFFFFFFFFFFF << tag;
    size_t ret = (size_t)ptr & mask;
    ret = ret | invert_tag;

    // if (invert_tag == 0) {
    //     fprintf(stderr, "[minfat_base_debug]: ptr without tag\n");
    // }
    // else {
    //     fprintf(stderr, "[minfat_base_debug]: ptr with tag\n");
    // }

    return (void*)ret;
}