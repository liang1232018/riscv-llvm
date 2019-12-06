#ifndef __SMA_H
#define __SMA_H

#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>

#define MINFAT_OOB_ERROR_READ              0
#define MINFAT_OOB_ERROR_WRITE             1
#define MINFAT_OOB_ERROR_MEMCPY            2
#define MINFAT_OOB_ERROR_MEMSET            3
#define MINFAT_OOB_ERROR_STRDUP            4
#define MINFAT_OOB_ERROR_ESCAPE_CALL       5
#define MINFAT_OOB_ERROR_ESCAPE_RETURN     6
#define MINFAT_OOB_ERROR_ESCAPE_STORE      7
#define MINFAT_OOB_ERROR_ESCAPE_PTR2INT    8
#define MINFAT_OOB_ERROR_ESCAPE_INSERT     9
#define MINFAT_PTR_INVALID                 0xA
#define MINFAT_OOB_ERROR_MEMCPY_ONE        0xB
#define MINFAT_OOB_ERROR_MEMCPY_TWO        0xC
#define MINFAT_OOB_ERROR_UNKNOWN           0xFF

#define MINFAT_TAG_MASK             (0xFC00000000000000)
#define MINFAT_PTR_MASK             (0x03FFFFFFFFFFFFFF)
#define MINFAT_BASE_SIZE            6
#define MINFAT_TAG_OFFSET           58

#endif      // __SMA_H