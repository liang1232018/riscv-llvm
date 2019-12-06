#include "minfat.h"

#include <errno.h>
#include <string.h>

#define MINFAT_ALIAS(name)      __attribute__((__alias__(name)))

// extern void *__libc_malloc(size_t size);
// extern void *__libc_realloc(void *ptr, size_t size);
// extern void __libc_free(void *ptr);

// TODO: Implement our own malloc() without POSIX function
extern int memalign(size_t alignment, size_t size);

static void *minfat_fallback_malloc(size_t size)
{
    void *ptr = malloc(size);
    if (ptr == NULL) {
        fprintf(stderr, " [MinFat]: Error! Memory allocation failed: %s\n", strerror(errno));
        abort();
    }
    return ptr;
}

#define minfat_fallback_free(x)             free(x)
#define minfat_fallback_realloc(x, y)       realloc((x), (y))

// int malloc_count = 0;
// int free_count = 0;

extern void *minfat_malloc(size_t size)
{
    if (size >= 0x1000000000000) {
        fprintf(stderr, "[minfat_malloc]: size is too large, 0x%lX\n", size);
        abort();
        // size = size & MINFAT_PTR_MASK;
    }
        
    // malloc_count++;
    // fprintf(stderr, "malloc: %d\n", malloc_count);
    if(size < 8) {
        size = 7;
    }

    size_t coded_size = (64 - clz(size)) & 0x3F;
    size_t alloc_size = 1ull << coded_size;
    void *ptr = NULL;
    // printf(" [debug]: in minifat_malloc, coded_size: %u, alloc_size: %u\n", coded_size, alloc_size);

    ptr = (void*)memalign(alloc_size, alloc_size);
    if (ptr == NULL) {
        fprintf(stderr, "[minfat_malloc]: failed, fallback\n");
        fprintf(stderr, "  size: %lu\n", size);
        fprintf(stderr, "  coded_size: %lu\n", coded_size);
        fprintf(stderr, "  alloc_size: %lu\n", alloc_size);
        return minfat_fallback_malloc(size);
    }
    else {
        coded_size = ~coded_size & 0x3F;
        ptr = (void*)((size_t)ptr | (coded_size << 58));
        // printf(" [minfat_malloc]: success, %p, size: %lu\n", ptr, alloc_size);
        return ptr;
    }
}

extern void minfat_free(void *ptr)
{
    // printf(" [minfat_free] input ptr: %p\n\n", ptr);
    // free_count++;
    // fprintf(stderr, "free: %d\n", free_count);
    free((void*)((size_t)ptr & MINFAT_PTR_MASK));
}

// 这段Alias可能导致把未插桩代码中的的这些函数替换掉，如果替换了malloc的话，其他未经插桩的代码会因为额外的tag而访存失败
// #ifdef __aarch64__
// extern void free(void *ptr) MINFAT_ALIAS("minfat_free");
// // extern void *realloc(void *ptr, size_t size) MINFAT_ALIAS("minfat_realloc");
// extern void _ZdlPv(void *ptr) MINFAT_ALIAS("minfat_free");
// extern void _ZdaPv(void *ptr) MINFAT_ALIAS("minfat_free");

// extern void *malloc(size_t size) MINFAT_ALIAS("minfat_malloc");
// extern void *calloc(size_t nmemb, size_t size) MINFAT_ALIAS("minfat_calloc");
// extern int posix_memalign(void **memptr, size_t align, size_t size)
//     MINFAT_ALIAS("minfat_posix_memalign");
// extern void *memalign(size_t align, size_t size)
//     MINFAT_ALIAS("minfat_memalign");
// extern void *valloc(size_t size) MINFAT_ALIAS("minfat_valloc");
// extern void *pvalloc(size_t size) MINFAT_ALIAS("minfat_pvalloc");
// extern void *_Znwm(size_t size) MINFAT_ALIAS("minfat_malloc");
// extern void *_Znam(size_t size) MINFAT_ALIAS("minfat_malloc");
// extern void *_ZnwmRKSt9nothrow_t(size_t size) MINFAT_ALIAS("minfat_malloc");
// extern void *_ZnamRKSt9nothrow_t(size_t size) MINFAT_ALIAS("minfat_malloc");
// #ifdef __strdup
// #undef __strdup
// #endif
// extern char *__strdup(const char *str) MINFAT_ALIAS("minfat_strdup");
// #ifdef __strndup
// #undef __strndup
// #endif
// extern char *__strndup(const char *str, size_t n)
//     MINFAT_ALIAS("minfat_strndup");

extern void *minfat_memalign(size_t align, size_t size)
{
    if (align > size) {
        return minfat_malloc(align);
    }
    else {
        return minfat_malloc(size);
    }
}

/*
 * MINFAT memset
 */
extern void *minfat_memset(void *dst, int c, size_t n)
{
    size_t size = minfat_buffer_size(dst);
    size_t tag = (size_t)dst & MINFAT_TAG_MASK;
    void *masked_dst = (void*)((size_t)dst & MINFAT_PTR_MASK);
    void *ret = NULL;
    if (size < n) {
        fprintf(stderr, " [MinFat]: memset out-of-bound!\n");
        ret = memset(masked_dst, c, size);
    }
    else {
        ret = memset(masked_dst, c, n);
    }
    ret = (void*)((size_t)ret | tag);
    return ret;
}

/*
 * MINFAT memmove
 */
extern void *minfat_memmove(void *dst, const void *src, size_t n)
{
    size_t src_size = minfat_buffer_size(src);
    if (src_size < n) {
        fprintf(stderr, "[minfat_memmove]: memcpy (src) out-of-bound!\n");
        fprintf(stderr, "  src_size: %lu, n: 0x%lx\n", src_size, n);
        fprintf(stderr, "  src: %p\n", src);
        abort();
        // n = src_size;
    }
    size_t dst_size = minfat_buffer_size(dst);
    size_t dst_tag = (size_t)dst & MINFAT_TAG_MASK;
    if (dst_size < n) {
        fprintf(stderr, "[minfat_memmove]: memcpy (dst) out-of-bound!\n");
        // size_t debug_size = minfat_size(dst);
        // size_t debug_base = minfat_base_rt(dst);
        // size_t debug_masked_ptr = (size_t)dst & MINFAT_PTR_MASK;
        // fprintf(stderr, "  size: %lu, base: 0x%lX, masked_ptr: 0x%lX\n", debug_size, debug_base, debug_masked_ptr);
        
        fprintf(stderr, "  dst_size: %lu, n: 0x%lx\n", dst_size, n);
        fprintf(stderr, "  dst: %p\n", dst);
        abort();
        // n = dst_size;
    }
    void *masked_dst = (void*)((size_t)dst & MINFAT_PTR_MASK);
    void *masked_src = (void*)((size_t)src & MINFAT_PTR_MASK);
    void *ret = memmove(masked_dst, masked_src, n);
    ret = (void*)((size_t)ret | dst_tag);
    return ret;
}

/*
 * MINFAT memcpy
 */
extern void *minfat_memcpy(void *dst, const void *src, size_t n)
{
    return minfat_memmove(dst, src, n);
}

extern void *minfat_realloc(void *ptr, size_t size)
{
    if (ptr == NULL || size == 0)
        return minfat_malloc(size);
    

    size_t dst_size;
    if (size < 8) {
        dst_size = 8;
    }
    else {
        dst_size = 1ull << ((64 - clz(size)) & 0x3F);
    }

    size_t src_size = 1ull << ((~(size_t)ptr >> 58) & 0x3F);
    if (~(size_t)ptr >> 58 != 0x3F) {
        dst_size = (dst_size < src_size ? dst_size : src_size);

        void *new_ptr = minfat_malloc(size);
        if (new_ptr == NULL) {
            return NULL;
        }

        minfat_memcpy(new_ptr, ptr, dst_size);
        minfat_free(ptr);
        ptr = NULL;

        return new_ptr;
    }
    else {
        // non-fat, fallback to __libc_realloc
        return realloc(ptr, size);
    }
}

extern void *minfat_calloc(size_t nmemb, size_t size)
{
    void *ptr = minfat_malloc(nmemb * size);
    minfat_memset(ptr, 0, nmemb * size);
    return ptr;
}

/*
 * MINFAT C++ new
 */
extern void *minfat__Znwm(size_t size) MINFAT_ALIAS("minfat_malloc");

/*
 * MINFAT C++ new[]
 */
extern void *minfat__Znam(size_t size) MINFAT_ALIAS("minfat_malloc");

/*
 * MINFAT C++ new nothrow
 */
extern void *minfat__ZnwmRKSt9nothrow_t(size_t size)
    MINFAT_ALIAS("minfat_malloc");

/*
 * MINFAT C++ new[] nothrow
 */
extern void *minfat__ZnamRKSt9nothrow_t(size_t size)
    MINFAT_ALIAS("minfat_malloc");

/*
 * MINFAT C++ delete
 */
extern void minfat__ZdlPv(void *ptr) MINFAT_ALIAS("minfat_free");

/*
 * MINFAT C++ delete[]
 */
extern void minfat__ZdaPv(void *ptr) MINFAT_ALIAS("minfat_free");

/*
 * MINFAT strdup()
 */
extern char *minfat_strdup(const char *str)
{
    size_t str_size = minfat_buffer_size(str);
    void *masked_str = (void*)((size_t)str & MINFAT_PTR_MASK);
    size_t len = strnlen(masked_str, str_size);

    // Can't find a '\0' within legal buffer size
    if (len == str_size) {
        fprintf(stderr, " [MinFat]: strdup out-of-bound!\n");
        abort();
    }

    char *str2 = (char *)minfat_malloc(len + 1); // strnlen doesn't count '\0'
    minfat_memcpy(str2, str, len + 1);
    return str2;
}

/*
 * MINFAT strndup()
 */
extern char *minfat_strndup(const char *str, size_t n)
{
    size_t str_size = minfat_buffer_size(str);
    void *masked_str = (void*)((size_t)str & MINFAT_PTR_MASK);
    size_t len = strnlen(masked_str, (n > str_size ? str_size : n));

    if (len == str_size) {
        fprintf(stderr, " [MinFat]: strndup out-of-bound!\n");
        abort();
    }

    char *str2 = (char *)minfat_malloc(len + 1);
    minfat_memcpy(str2, str, len);
    str2[len] = '\0';
    return str2;
}