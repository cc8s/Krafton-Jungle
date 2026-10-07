#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/* mdriver 가 출력에 쓰는 팀 정보 — 지우면 링크 에러(undefined reference to `team`) */
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

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* 매크로 추가 */
#define WSIZE 4
#define DSIZE 8

/* 헤더에 쓸값 = 4바이트(할당된 블럭 크기+할당됐는지 여부) */
#define PACK(size, alloc)   ((size) | (alloc))
/* */
#define GET(p)              (*(unsigned int *)(p))
#define PUT(p, val)         ((*(unsigned int *)(p) = (val)))
/* 비트연산 GET_SIZE는 마지막 3비트 제외 나머지 비트 연산
   GET_ALLOC은 마지막 1비트만 남김*/
#define GET_SIZE(p)         (GET(p) & ~0x7)
#define GET_ALLOC(p)        (GET(p) & 0x1)
/* 헤더 구하기 = bp포인터단위(1) - WSIZE(4바이트) */
#define HDRP(bp)             ((char *)(bp) - WSIZE)
/* bp의 푸터 주소 (헤더의 크기를 이용) */
#define FTRP(bp)             ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
/* 다음 블록 페이로드 주소 */
#define NEXT_BLKP(bp)        ((char *)(bp) + GET_SIZE(HDRP(bp)))
/* 전 블록 페이로드 주소 */
#define PREV_BLKP(bp)        ((char *)(bp) - GET_SIZE((char *)(bp) - DSIZE))

#define CHUNKSIZE 4096
#define MAX(x, y)            ((x) > (y) ? (x) : (y))

static char *heap_listp;    /* 프롤로그 bp */
static char *rover;    
static void *extend_heap(size_t words);
static void *coalesce(void *bp);

static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

/*
 * mm_init - initialize the malloc package.
    1. mem_sbrk로 16바이트를 받아서 heap_listp에 저장. 실패하면 -1
    2. PUT 네 줄 (pad, prologue 헤더, prologue 푸터, epilogue 헤더)
    3. heap_listp를 prologue의 bp 위치로 옮김
    4. extend_heap 호출 (아직 안 만들었으니 지금은 주석 처리)
 */
int mm_init(void)
{
    heap_listp = mem_sbrk(4 * WSIZE);
    if (heap_listp == (void *)-1)
        return -1;
    
    PUT(heap_listp, 0);
    PUT(heap_listp + WSIZE, PACK(8, 1));
    PUT(heap_listp + DSIZE, PACK(8, 1));
    PUT(heap_listp + 3 * WSIZE, PACK(0, 1));

    heap_listp += DSIZE;
    rover = heap_listp;

    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    return 0;
}

void *mm_malloc(size_t size)
{
    size_t asize;       /* 실제 블록 크기 */
    size_t extendsize;  /* 맞는 블록이 없을 때 늘릴 크기 */
    char *bp;

    if (size == 0)
        return NULL;

    /* 1. asize 계산
         size가 DSIZE 이하면 최소 블록 크기(2 * DSIZE)
         아니면 (size + 헤더·푸터 8바이트)를 8의 배수로 올림 */
    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = ALIGN(size + DSIZE);
    /* 2. find_fit으로 찾으면 → place 하고 bp 반환 */
    bp = find_fit(asize);
    if (bp != NULL) {
        place(bp, asize);
        return bp;
    }
    
    extendsize = MAX(asize, CHUNKSIZE);

    bp = extend_heap(extendsize / WSIZE);
    if (bp == NULL)
        return NULL;
    place(bp, asize);
    return bp;
    /* 3. 없으면 extendsize = MAX(asize, CHUNKSIZE)
         extend_heap(extendsize를 word 개수로) → 실패하면 NULL
         place 하고 bp 반환 */
}

void mm_free(void *ptr)
{   
    if (ptr == NULL)
        return;

    unsigned int size = GET_SIZE(HDRP(ptr));    /* ptr 블록의 크기 (헤더에서 읽기) */

    PUT(HDRP(ptr), PACK(size, 0));  /* 1. 헤더를 (size, 0)으로 */
    PUT(FTRP(ptr), PACK(size, 0));  /* 2. 푸터를 (size, 0)으로 */

    coalesce(ptr);  /* ③ 이웃 빈 블록과 합치기 */
}

void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;

    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;
    copySize = GET_SIZE(HDRP(oldptr)) - DSIZE;
    if (size < copySize)
        copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}
/* 힙 늘리기 */
    /* size 계산: words가 홀수면 +1, 그다음 × WSIZE */
    /* mem_sbrk로 size바이트 받기 → bp. 실패하면 NULL 반환 */
    /* 1. 새 헤더 (옛 epilogue 자리) */
    /* 2. 새 푸터 */
    /* 3. 새 epilogue */
static void *extend_heap(size_t words)
{
    size_t size;
    char *bp;

    if (words % 2 != 0) {
        size = (words + 1) * WSIZE;
    } else {
        size = words * WSIZE;
    }

    bp = mem_sbrk(size);
    if (bp == (void *)-1)
        return NULL;

    /*새 헤더*/
    PUT(HDRP(bp), PACK(size, 0));
    /*새 풋터*/
    PUT(FTRP(bp), PACK(size, 0));
    /*extended epilogue*/
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    return coalesce(bp);
}

static void *coalesce(void *bp)
{
    unsigned int size = GET_SIZE(HDRP(bp));
    unsigned int next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    unsigned int prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(bp)));

    if (prev_alloc == 1 && next_alloc == 1) {          /* 앞뒤 모두 사용중 */
        return bp;
    } else if (prev_alloc == 1 && next_alloc == 0) {   /* 앞 사용중, 뒤 빈블럭 */
        size = size + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    } else if (prev_alloc == 0 && next_alloc == 1) {   /* 앞 빈블럭, 뒤 사용중 */
        size = size + GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        bp = PREV_BLKP(bp);
    } else {                                           /* 앞뒤 모두 빈블 */
        size = size + GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    if (rover > (char *)bp && rover < NEXT_BLKP(bp))
        rover = bp;
    return bp;
}

static void *find_fit(size_t asize)
{
    char *oldrover = rover;

    /* 1바퀴: rover부터 epilogue까지 */
    for (; GET_SIZE(HDRP(rover)) > 0; rover = NEXT_BLKP(rover))
        if (GET_ALLOC(HDRP(rover)) == 0 && GET_SIZE(HDRP(rover)) >= asize)
            return rover;

    /* 2바퀴: 처음부터 oldrover 직전까지 */
    for (rover = heap_listp; rover < oldrover; rover = NEXT_BLKP(rover))
        if (GET_ALLOC(HDRP(rover)) == 0 && GET_SIZE(HDRP(rover)) >= asize)
            return rover;

    return NULL;
}

static void place(void *bp, size_t asize)
{
    unsigned int csize = GET_SIZE(HDRP(bp));  /* 지금 빈 블록의 전체 크기 */

if (csize - asize >= 2 * DSIZE) {/* 남는 크기(csize - asize)가 최소 블록 크기 이상이라면 */
        /* 1. 앞부분 헤더를 (asize, 1)로 */
        PUT(HDRP(bp), PACK(asize, 1));
        /* 2. 앞부분 푸터를 (asize, 1)로 */
        PUT(FTRP(bp), PACK(asize, 1));
        /* 3. bp를 남은 부분의 bp로 옮김. 여기서 옮겼으니 다음부분 = 현재bp가 됌. */
        bp = NEXT_BLKP(bp);
        /* 4. 남은 부분 헤더를 (csize - asize, 0)으로 */
        PUT(HDRP(bp), PACK(csize - asize, 0));
        /* 5. 남은 부분 푸터를 (csize - asize, 0)으로 */
        PUT(FTRP(bp), PACK(csize - asize, 0));
    } else {
        /* 통째로 줌: 헤더와 푸터를 (csize, 1)로 */
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}