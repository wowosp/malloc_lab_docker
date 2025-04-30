#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>
#include "mm.h"
#include "memlib.h"

team_t team = {
    "ateam",
    "Harry Bovik",
    "bovik@cs.cmu.edu",
    "",
    ""
};

#define ALIGNMENT 8
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1<<12)
#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define PACK(size, alloc) ((size) | (alloc))
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE((char *)(bp) - DSIZE))
#define NEXT_FREE(bp) (*(char **)(bp + WSIZE))
#define PREV_FREE(bp) (*(char **)(bp))

#define LISTLIMIT 16

static char *heap_listp = 0;
static void *segregated_free_list[LISTLIMIT];

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void add_freelist(void *bp);
static void delete_freelist(void *bp);
static int get_list_index(size_t size);

static int get_list_index(size_t size) {
    if (size <= 16) return 0;
    else if (size <= 32) return 1;
    else if (size <= 64) return 2;
    else if (size <= 128) return 3;
    else if (size <= 256) return 4;
    else if (size <= 512) return 5;
    else if (size <= 1024) return 6;
    else if (size <= 2048) return 7;
    else if (size <= 4096) return 8;
    else if (size <= 8192) return 9;
    else if (size <= 16384) return 10;
    else if (size <= 32768) return 11;
    else if (size <= 65536) return 12;
    else if (size <= 131072) return 13;
    else if (size <= 262144) return 14;
    else return 15;
}

int mm_init(void) {
    int list;
    for (list = 0; list < LISTLIMIT; list++) {
        segregated_free_list[list] = NULL;
    }

    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0);
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));
    
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}

static void *extend_heap(size_t words) {
    char *bp;
    size_t size = (words % 2) ? (words+1)*WSIZE : words*WSIZE;
    if ((bp = mem_sbrk(size)) == (void *)-1)
        return NULL;
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));
    return coalesce(bp);
}

void *mm_malloc(size_t size) {
    size_t asize, extendsize;
    char *bp;
    if (size == 0) return NULL;
    asize = (size <= DSIZE) ? 2*DSIZE : DSIZE*((size + DSIZE + DSIZE-1)/DSIZE);
    if ((bp = find_fit(asize))) {
        place(bp, asize);
        return bp;
    }
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

void mm_free(void *bp) {
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

static void *coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (!prev_alloc && !next_alloc) {
        delete_freelist(PREV_BLKP(bp));
        delete_freelist(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    } else if (!prev_alloc) {
        delete_freelist(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    } else if (!next_alloc) {
        delete_freelist(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    add_freelist(bp);
    return bp;
}

void *mm_realloc(void *ptr, size_t size) {
    if (ptr == NULL) return mm_malloc(size);
    if (size == 0) {
        mm_free(ptr);
        return NULL;
    }
    void *newptr = mm_malloc(size);
    if (!newptr) return NULL;
    size_t oldsize = GET_SIZE(HDRP(ptr));
    memcpy(newptr, ptr, oldsize < size ? oldsize : size);
    mm_free(ptr);
    return newptr;
}

static void *find_fit(size_t asize) {
    int start_index = get_list_index(asize);
    
    for (int i = start_index; i < LISTLIMIT; i++) {
        void *bp = segregated_free_list[i];
        while (bp != NULL) {
            if (!GET_ALLOC(HDRP(bp)) && asize <= GET_SIZE(HDRP(bp))) {
                return bp;
            }
            bp = NEXT_FREE(bp);
        }
    }
    return NULL;
}

static void place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp));
    delete_freelist(bp);
    if ((csize - asize) >= 2*DSIZE) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        void *remaining = NEXT_BLKP(bp);
        PUT(HDRP(remaining), PACK(csize - asize, 0));
        PUT(FTRP(remaining), PACK(csize - asize, 0));
        add_freelist(remaining);
    } else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

static void add_freelist(void *bp) {
    size_t size = GET_SIZE(HDRP(bp));
    int index = get_list_index(size);

    NEXT_FREE(bp) = segregated_free_list[index];
    PREV_FREE(bp) = NULL;

    if (segregated_free_list[index] != NULL) {
        PREV_FREE(segregated_free_list[index]) = bp;
    }

    segregated_free_list[index] = bp;
}

static void delete_freelist(void *bp) {
    size_t size = GET_SIZE(HDRP(bp));
    int index = get_list_index(size);

    if (segregated_free_list[index] == bp) {
        segregated_free_list[index] = NEXT_FREE(bp);
        if (segregated_free_list[index] != NULL) {
            PREV_FREE(segregated_free_list[index]) = NULL;
        }
    } else {
        if (NEXT_FREE(bp) != NULL) {
            PREV_FREE(NEXT_FREE(bp)) = PREV_FREE(bp);
        }
        if (PREV_FREE(bp) != NULL) {
            NEXT_FREE(PREV_FREE(bp)) = NEXT_FREE(bp);
        }
    }
}
