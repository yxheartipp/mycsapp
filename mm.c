/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE 4
#define DSIZE 8

#define CHUNKSIZE (1 << 12)

#define MAX(x, y) ((x) > (y)? (x) : (y))

#define PACK(size, alloc) ((size) | (alloc))

#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) ((*(unsigned int *)(p)) = (val))

#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

#define HDRP(bp) ((char*)(bp) - WSIZE)
#define FTRP(bp) ((char*)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define NEXT_BLKP(bp) ((char*)(bp) + GET_SIZE(((char*)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char*)(bp) - GET_SIZE(((char*)(bp) - DSIZE)))

#define GET_PREV(p) (*(unsigned int *)(p))
#define GET_NEXT(p) (*((unsigned int *)(p)+1))

#define SET_PREV(p,prev) (*(unsigned int *)(p) = (prev))
#define SET_NEXT(p,next) (*((unsigned int *)(p)+1) = (next)) 


static char *heap_listp;
static char *free_listp;

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp,size_t asize);
static void remove_list(void *bp);
static void insert_freelist(void *bp);



/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1) {
        return -1;
    }

    PUT(heap_listp,0);
    PUT(heap_listp+(1*WSIZE),PACK(DSIZE,1));
    PUT(heap_listp+(2*WSIZE),PACK(DSIZE,1));
    PUT(heap_listp+(3*WSIZE),PACK(0,1));

    heap_listp += (2*WSIZE);
    free_listp = NULL;


    #ifdef DEBUG
        printf("the size of head_listp :%x\n",GET_SIZE(HDRP(head_listp)));
        printf("the alloc of head_listp: %x\n",GET_ALLOC(FTRP(head_listp)));
    #endif

    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) {
        return -1;
    }
    #ifdef DEBUG
        printf("the size of freelist_head=%d\n",GET_SIZE(HDRP(freelist_head)));
    #endif
    return 0;
}

void *extend_heap(size_t words)
{
    char *bp;
    size_t size;
    size =  (words%2) ? (words+1) * WSIZE : words * WSIZE;

    if ((long)(bp = mem_sbrk(size)) == -1) {
        return NULL;
    }

    PUT(HDRP(bp),PACK(size,0));
    PUT(FTRP(bp),PACK(size,0));
    SET_NEXT(bp,0);
    SET_PREV(bp,0);  //申请出来的新空闲块不在空闲表中
    PUT(HDRP(NEXT_BLKP(bp)),PACK(0,1));
    #ifdef DEBUG
        printf("the freelist_head size is :%d\n",GET_SIZE(HDRP(freelist_head)));
    #endif
    return coalesce(bp);
}

void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    void* prev_bp = PREV_BLKP(bp);
    void* next_bp = NEXT_BLKP(bp);
    size_t size = GET_SIZE(HDRP(bp));

    if(prev_alloc && next_alloc) {
        insert_freelist(bp);
        return bp;
    } else if (prev_alloc && !next_alloc) {
        remove_list(next_bp);
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp),PACK(size,0));
        PUT(FTRP(bp),PACK(size,0));
    } else if (!prev_alloc && next_alloc) {
        remove_list(prev_bp);
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp),PACK(size,0));
        PUT(HDRP(PREV_BLKP(bp)),PACK(size,0));
        bp = PREV_BLKP(bp);
    } else {
        remove_list(next_bp);
        remove_list(prev_bp);
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))); 
        PUT(FTRP(NEXT_BLKP(bp)),PACK(size,0));
        PUT(HDRP(PREV_BLKP(bp)),PACK(size,0));
        bp = PREV_BLKP(bp);
    }
    insert_freelist(bp);
    // 考虑写一个heap checker
    return bp;
}

static void remove_list(void *bp)
{
    if (bp == NULL || GET_ALLOC(HDRP(bp))) {
        return;
    }

    void *prev = GET_PREV(bp);
    void *next = GET_NEXT(bp);
    SET_PREV(bp,0);
    SET_NEXT(bp,0);
    if (prev == NULL && next == NULL) {
        free_listp = NULL;
    } else if (prev == NULL) {
        free_listp = next;
        SET_PREV(next,0);
    } else if (next == NULL) {
        SET_NEXT(prev,0);
    } else {
        SET_NEXT(prev,next);
        SET_PREV(next,prev);
    }
}

static void insert_freelist(void *bp)
{
    if (bp == NULL) {
        return;
    }
    if (free_listp==NULL) {
        free_listp = bp;
        return;
    }
    SET_NEXT(bp,free_listp);
    SET_PREV(free_listp,bp);
    free_listp = bp;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;
    if (size == 0) {
        return NULL;
    }
    if (size <= DSIZE) {
        asize = 2*DSIZE;
    } else {
        asize = DSIZE * ((size+(DSIZE)+(DSIZE-1))/DSIZE);
    }
    if((bp = find_fit(asize)) != NULL){
        place(bp, asize);
        return bp;
    }
    extendsize = MAX(asize,CHUNKSIZE);
    if((bp = extend_heap(extendsize/WSIZE)) == NULL) {
        return NULL;
    }
    place(bp,asize);
    return bp;
}

void *find_fit(size_t asize)
{
    for (void *bp = free_listp;bp != 0;bp = GET_NEXT(bp)) {
        if (GET_SIZE(HDRP(bp)) >= asize) {
            return bp;
        }
    }
    return NULL;
}

void place(void *bp,size_t asize)
{
    size_t size = GET_SIZE(HDRP(bp));
    remove_list(bp);

    if ((size-asize) >= 2*DSIZE) {
        PUT(HDRP(bp),PACK(asize,1));
        PUT(FTRP(bp),PACK(asize,1));
        void *new_bp = NEXT_BLKP(bp);
        PUT(HDRP(new_bp),PACK(size-asize,0));
        PUT(FTRP(new_bp),PACK(size-asize,0));
        SET_PREV(new_bp,0);
        SET_NEXT(new_bp,0);
        coalesce(new_bp);
    } else {
        PUT(HDRP(bp), PACK(size, 1));
        PUT(FTRP(bp), PACK(size, 1));
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    if (ptr == 0) {
        return;
    }
    size_t size = GET_SIZE(HDRP(ptr));
    PUT(HDRP(ptr),PACK(size,0));
    PUT(FTRP(ptr),PACK(size,0));
    SET_NEXT(ptr,0);
    SET_PREV(ptr,0);
    coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;

    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    size = GET_SIZE(HDRP(oldptr));
    copySize = GET_SIZE(HDRP(newptr));
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize-WSIZE);
    mm_free(oldptr);
    return newptr;
}














