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
#include <limits.h>
#include "mm.h"
#include "memlib.h"
#include <math.h>

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/

/* Basic constants and macros */
#define WSIZE 4 /* Word and header/footer size (bytes) */ //
#define DSIZE 8                                           /* Double word size (bytes) */
#define CHUNKSIZE (1 << 8)                               /* Extend heap by this amount (bytes) */

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp)-WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

// 포인터 할당 매크로
#define SET_PREV(bp, addr) (*(void **)(bp) = (addr))
#define SET_NEXT(bp, addr) (*(void **)(bp + WSIZE) = (addr))

// 포인터 좌우 이동 매크로
#define PREV_FREE(bp) (*(void **)(bp))
#define NEXT_FREE(bp) (*(void **)(bp + WSIZE))

// 2의 제곱수 구하기
#define get_index(x) 31 - __builtin_clz(x)

#define DIV 22
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
    ""};

static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static char *heap_listp;
static void *head;
static char *free_cursor;
static void *B_S[25];

static void add_free(void *bp)
{
    int freeSize = GET_SIZE(HDRP(bp));
    int bn = get_index(freeSize);

    if (bn > DIV)
        bn = DIV + 1;

    void *tmp = B_S[bn];
    B_S[bn] = bp;
    SET_NEXT(bp, tmp);
    SET_PREV(tmp, bp);
}

static void remove_free(void *bp)
{

    int freeSize = GET_SIZE(HDRP(bp));
    int bn = get_index(freeSize);

    if (bn > DIV)
        bn = DIV + 1;

    if (bp == B_S[bn])
    {
        B_S[bn] = NEXT_FREE(bp);
    }
    else
    {
        void *prev = PREV_FREE(bp);
        void *next = NEXT_FREE(bp);
        SET_NEXT(prev, next);
        SET_PREV(next, prev);
    }
}

static void *find_fit(size_t asize)
{
    int bn = get_index(asize);

    if (bn > DIV)
        bn = DIV + 1;

    for (int i = bn; i <= DIV + 1; i++)
    {
        for (void *cur = B_S[i]; NEXT_FREE(cur) != NULL; cur = NEXT_FREE(cur))
        {
            if (asize <= GET_SIZE(HDRP(cur)))
            {
                return cur;
            }
        }
    }
    return NULL;
}
/*
static void place(void *bp, size_t asize)
{
    size_t free_size = GET_SIZE(HDRP(bp));
    if (free_size - asize >= DSIZE * 2)
    {
        remove_free(bp);
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));

        bp = NEXT_BLKP(bp);

        PUT(HDRP(bp), PACK(free_size - asize, 0));
        PUT(FTRP(bp), PACK(free_size - asize, 0));
        add_free(bp);
        // free_cursor = bp;
    }
    else
    {
        remove_free(bp);
        PUT(HDRP(bp), PACK(free_size, 1));
        PUT(FTRP(bp), PACK(free_size, 1));
        // free_cursor = bp;
    }
}
*/
static void place(void *bp, size_t asize)
{
    size_t free_size = GET_SIZE(HDRP(bp));
    // printf("플레이스: free_size:%d, asize: %d\n", free_size, asize);
    if (free_size != asize)
    {
        remove_free(bp);
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));

        bp = NEXT_BLKP(bp);
        free_size -= asize;
        while (1)
        {
            int tmp = get_index(free_size);
            if (1 << tmp == free_size)
            {
                PUT(HDRP(bp), PACK(free_size, 0));
                PUT(FTRP(bp), PACK(free_size, 0));
                add_free(bp);
                return;
            }
            else
            {
                tmp--;
                int temp_size = 1 << (tmp);
                PUT(HDRP(bp), PACK(temp_size, 0));
                PUT(FTRP(bp), PACK(temp_size, 0));
                add_free(bp);
                bp = NEXT_BLKP(bp);
                free_size -= temp_size;
            }
        }
    }
    else
    {
        remove_free(bp);
        PUT(HDRP(bp), PACK(free_size, 1));
        PUT(FTRP(bp), PACK(free_size, 1));
    }
}

static void *coalesce_sub(void *bp)
{

    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc)
    { /* Case 1 */
        add_free(bp);
        return bp;
    }

    else if (prev_alloc && !next_alloc)
    { /* Case 2 */
        remove_free(NEXT_BLKP(bp));

        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    else if (!prev_alloc && next_alloc)
    { /* Case 3 */
        remove_free(PREV_BLKP(bp));

        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));

        bp = PREV_BLKP(bp);
    }

    else
    { /* Case 4 */
        remove_free(NEXT_BLKP(bp));
        remove_free(PREV_BLKP(bp));

        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
                GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    free_cursor = bp;
    add_free(bp);
    return bp;
}

static void *coalesce(void *bp)
{

    // size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    // size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));

    // size_t prev_size = GET_SIZE(FTRP(PREV_BLKP(bp)));
    // size_t next_size = GET_SIZE(HDRP(NEXT_BLKP(bp)));


    if (GET_ALLOC(FTRP(PREV_BLKP(bp))) && GET_ALLOC(HDRP(NEXT_BLKP(bp))))
    { /* Case 1 */
        // printf("꼴뚜기 주소: %p, size: %d\n", bp, size);
        add_free(bp);
        return bp;
    }
    else
    {
        while (1)
        {
            size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
            size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));

            size_t prev_size = GET_SIZE(FTRP(PREV_BLKP(bp)));
            size_t next_size = GET_SIZE(HDRP(NEXT_BLKP(bp)));

            size_t size = GET_SIZE(HDRP(bp));
            if (prev_alloc && !next_alloc && size == next_size)
            { /* Case 2 */
                remove_free(NEXT_BLKP(bp));
                size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
                PUT(HDRP(bp), PACK(size, 0));
                PUT(FTRP(bp), PACK(size, 0));
            }

            else if (!prev_alloc && next_alloc && size == prev_size)
            { /* Case 3 */

                remove_free(PREV_BLKP(bp));

                size += GET_SIZE(HDRP(PREV_BLKP(bp)));
                PUT(FTRP(bp), PACK(size, 0));
                PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));

                bp = PREV_BLKP(bp);
            }
            else
            {
                break;
            }
        }

        // printf("꼴뚜기 주소: %p, size: %d\n", bp, size);
        add_free(bp);
        return bp;
    }
}

int cnt = 0;
int max = 0;
static void *extend_heap(size_t words)
{
    cnt+=words;
    max = MAX(max,cnt);
    printf("%d\n",words);
    // printf("확장%d\n", words * 4);
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

    /* Coalesce if the previous block was free */
    // if(size>(1<<DIV))
    //     return coalesce_sub(bp);
    // else
        return coalesce(bp);
}

/*
 * mm_init - initialize the malloc package.
 */

int mm_init(void)
{

    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk((DIV+1) * DSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0);                                 /* Alignment padding */
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE * (DIV+1), 1)); /* Prologue header */

    // SET_PREV(heap_listp + (2 * WSIZE), NULL); /*페이로드 주소 포인터 세팅*/
    // SET_PREV(heap_listp + (3 * WSIZE), NULL);
    int i = 2;
    for ( j = 0; i < DIV*2; i += 2, j++)
    {
        // printf("%d\n", j);
        SET_PREV(heap_listp + (i * WSIZE), NULL); /*페이로드 주소 포인터 세팅*/
        SET_PREV(heap_listp + (i + 1 * WSIZE), NULL);
        B_S[j] = heap_listp + (i * WSIZE);
    }

    PUT(heap_listp + (i * WSIZE), PACK(DSIZE * (DIV+1), 1)); /* Prologue footer */
    PUT(heap_listp + (++i * WSIZE), PACK(0, 1));          /* Epilogue header */
    // heap_listp += (2 * WSIZE);
    head = heap_listp;
    free_cursor = heap_listp;
    // printf("%p, %p\n",PREV_FREE(point_cursor),NEXT_FREE(point_cursor));

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */


void *mm_malloc(size_t size)
{
    cnt = 0;
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;

    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    // while (1)
    // {
    // scanf("%d", &asize);
    int class = get_index(asize);
    if (asize > (1 << class))
        class ++;
    if (class <= DIV)
        asize = (1 << class);
    else
    {
        // printf("어사이즈:%d\n", asize);
    }
    // printf("말록했다!: %d\n", asize);
    // printf("결정:%d\n", asize);

    // }

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    // remove_free(bp);
    // if(size>(1<<DIV))
    //     coalesce_sub(bp);
    // else
        coalesce(bp);
}

static void *re_place(void *bp, size_t asize, size_t totalSize)
{
    free_cursor = bp;
    // if (totalSize - asize >= DSIZE * 2)
    if (0)
    {
        // printf("크다 토탈 %d, 아싸 %d\n", totalSize, asize);
        remove_free(bp);
        PUT(HDRP(bp), PACK(asize, 1));
        // printf("헤드 사이즈:%d\n",GET_SIZE(HDRP(bp)));
        PUT(FTRP(bp), PACK(asize, 1));

        bp = NEXT_BLKP(bp);

        PUT(HDRP(bp), PACK(totalSize - asize, 0));
        PUT(FTRP(bp), PACK(totalSize - asize, 0));
        // printf("사용량:%d\n",asize+totalSize-asize);
    }
    else
    {
        // printf("작다\n");
        remove_free(NEXT_BLKP(bp));
        PUT(HDRP(bp), PACK(totalSize, 1));
        PUT(FTRP(bp), PACK(totalSize, 1));
    }
    return free_cursor;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    size_t oldSize = GET_SIZE(HDRP(ptr));

    // 새로 필요한 공간 계산
    size_t reSize;
    if (size <= DSIZE)
        reSize = 2 * DSIZE;
    else
        reSize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    // 일단 작은경우 제외
    // if (reSize <= oldSize)
    // {
    //     // printf("줄여\n");
    //     // re_place(ptr,reSize,oldSize);
    //     return ptr;
    // }

    // // // 다음 블럭이 free인 경우
    // void *nextPtr = NEXT_BLKP(ptr);
    // size_t nextSize = GET_SIZE(HDRP(nextPtr));
    // int isNextFree = GET_ALLOC(HDRP(nextPtr));
    // // 현재 공간과 다음 공간의 합
    // size_t totalSize = oldSize + nextSize;
    // if (isNextFree == 0)
    // {
    //     if (reSize <= totalSize)
    //     {
    //         // printf("요청 크기:%d, %d\n",size,reSize);
    //         return re_place(ptr, reSize, totalSize);
    //         // PUT(HDRP(ptr), PACK(totalSize, 1));
    //         // PUT(FTRP(ptr), PACK(totalSize, 1));
    //         // free_cursor = ptr;
    //         // return ptr;
    //     }
    // }

    //=======================

    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;
    copySize = GET_SIZE(HDRP(ptr));
    if (size < copySize)
        copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}