/*
 * mm_allocator.c
 *
 * Header Comment:
 * This program is competent with completing tasks such
 * as mallocing and freeing blocks with improved utility
 * and acceptable throughput.
 * This program uses both explicit lists and segregated
 * lists techniques--free blocks are organized by 15 lists
 * based on their sizes. Everytime we use the malloc function,
 * we first search in segregated lists to find whether there
 * exists free blocks that suffice our need. If so, remove the 
 * free block from lists, place the size into the block and 
 * decide whether to move the left place into lists based on 
 * its size. Also, the footers of the allocated blocks are 
 * removed to achieve better utility--using one of the lower 
 * three bytes of the header.
 * 
 * Also, the program combines the free blocks that are 
 * found consecutive in heap.
 * 
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
#define DEBUG
#ifdef DEBUG
#define dbg_printf(...) printf(__VA_ARGS__)
#else
#define dbg_printf(...)
#endif

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT - 1)) & ~0x7)

#define WSIZE 4             /* Word and header/footer size (bytes) */
#define DSIZE 8             /* Double word size (bytes) */
#define CHUNKSIZE (1 << 12) /* Extend heap by this amount (bytes) */

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, prex, alloc) ((size) | (prex) | (alloc))

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

/* check whether the prev block is allocated*/
#define PREVX(bp) (GET(bp) & 0x4)

/* define the boundaries of lists */
#define num01 12
#define num02 16
#define num03 20
#define num04 64
#define num05 112
#define num06 120
#define num07 256
#define num08 448
#define num09 512
#define num10 1024
#define num11 2048
#define num12 3072
#define num13 4096
#define num14 8192

/* the start of the heap */
static char *heap_listp = 0;

/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void* place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void insertx(void *bp, size_t asize);
static void deletex(void *bp, size_t asize);
void mm_checkheap(int lineno);

/* define the groups of the lists */
static size_t *list_start = 0;
static size_t *l01 = 0;
static size_t *l02 = 0;
static size_t *l03 = 0;
static size_t *l04 = 0;
static size_t *l05 = 0;
static size_t *l06 = 0;
static size_t *l07 = 0;
static size_t *l08 = 0;
static size_t *l09 = 0;
static size_t *l10 = 0;
static size_t *l11 = 0;
static size_t *l12 = 0;
static size_t *l13 = 0;
static size_t *l14 = 0;
static size_t *l15 = 0;

/*
 * Initialize: initialize the heap and lists
 * return -1 on error, 0 on success.
 */
int mm_init(void)
{
    /* Create the initial empty heap */
    list_start = NULL;
    l01 = NULL;
    l02 = NULL;
    l03 = NULL;
    l04 = NULL;
    l05 = NULL;
    l06 = NULL;
    l07 = NULL;
    l08 = NULL;
    l09 = NULL;
    l10 = NULL;
    l11 = NULL;
    l12 = NULL;
    l13 = NULL;
    l14 = NULL;
    l15 = NULL;

    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;

    PUT(heap_listp, 0);                               /* Alignment padding */
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 4, 1)); /* Prologue header */
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 4, 1)); /* Prologue footer */
    PUT(heap_listp + (3 * WSIZE), PACK(0, 4, 1));     /* Epilogue header */
    heap_listp += (2 * WSIZE);

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;

    return 0;
}

/*
 * malloc: used when the user declared the usage 
 * of a new place in heap.
 * If the heap is empty, initialize the heap.
 * If not, find the block that may suffice the need.
 * If the block does not exists, extend the heap.
 * If the block exists, place the required size into
 * the block.
 */
void *malloc(size_t size)
{
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;
    if (heap_listp == 0)
    {
        mm_init();
    }
    /* Ignore spurious requests */
    if (size <= 0)
        return NULL;
    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * (((WSIZE) + size + (DSIZE - 1)) / DSIZE);

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL)
    {
        bp = place(bp, asize);
        return bp;
    }
    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    
    /* the bp may be modified */
    bp = place(bp, asize);
    return bp;
}

/*
 * free: used when the user declared to free one of 
 * the malloced place.
 * Add the free block to lists.
 */
void free(void *ptr)
{
    if (ptr == 0)
        return;
    if (heap_listp == 0)
    {
        mm_init();
    }
    size_t size = GET_SIZE(HDRP(ptr));
    size_t checkprev = PREVX(HDRP(ptr));
    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(ptr), PACK(size, checkprev, 0)); /* Free block header */
    PUT(FTRP(ptr), PACK(size, checkprev, 0)); /* Free block footer */
    /* change the state of the next block to indicate that its previous block is not allocated */
    if (GET_ALLOC(HDRP(NEXT_BLKP(ptr))))
    {
        PUT(HDRP(NEXT_BLKP(ptr)), PACK(GET_SIZE(HDRP(NEXT_BLKP(ptr))), 0, 1)); 
        /* Coalesce if the previous block was free */
        coalesce(ptr);
    }
    else
    {
        PUT(HDRP(NEXT_BLKP(ptr)), PACK(GET_SIZE(HDRP(NEXT_BLKP(ptr))), 0, 0)); /* New epilogue header */
        PUT(FTRP(NEXT_BLKP(ptr)), PACK(GET_SIZE(HDRP(NEXT_BLKP(ptr))), 0, 0)); /* New epilogue header */
        /* Coalesce if the previous block was free */
        coalesce(ptr);
    }
}

/*
 * realloc - Change the size of the block by mallocing 
 * a new block, copying its data, and freeing the old 
 * block.  
 */
void *realloc(void *oldptr, size_t size)
{
    size_t oldsize;
    void *newptr;
    /* If size == 0 then this is just free, and we return NULL. */
    if (size == 0)
    {
        mm_free(oldptr);
        return 0;
    }
    /* If oldptr is NULL, then this is just malloc. */
    if (oldptr == NULL)
    {
        return mm_malloc(size);
    }
    newptr = mm_malloc(size);
    /* If realloc() fails the original block is left untouched  */
    if (!newptr)
    {
        return 0;
    }
    /* Copy the old data. */
    oldsize = GET_SIZE(HDRP(oldptr));
    if (size < oldsize)
        oldsize = size;
    memcpy(newptr, oldptr, oldsize);
    /* Free the old block. */
    mm_free(oldptr);
    return newptr;
}

/*
 * calloc - Allocate the block and set it to zero.
 */
void *calloc(size_t nmemb, size_t size)
{
    size_t bytes = nmemb * size;
    void *newptr;
    newptr = malloc(bytes);
    memset(newptr, 0, bytes);
    return newptr;
}

/*
 * Return whether the pointer is in the heap.
 */
static int in_heap(const void *p)
{
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Return whether the pointer is aligned.
 */
static int aligned(const void *p)
{
    return (size_t)ALIGN(p) == (size_t)p;
}

/*
 * mm_checkheap-check the status of the heap
 * and the segregated lists.
 */
void mm_checkheap(int lineno)
{
    char* bp = heap_listp;
    if (lineno)
    {
        printf("Heap starts at %p\n", bp);
    }
    if (!GET(HDRP(heap_listp)))
    {
        printf("Epilogue And Prologue Blocks Error!\n");
        exit(0);
    }
    if ((GET_SIZE(HDRP(heap_listp))) != DSIZE)
    {
        printf("Epilogue And Prologue Size Error!\n");
        exit(0);
    }
    if ((GET_ALLOC(HDRP(heap_listp))) == 0)
    {
        printf("Epilogue And Prologue Header Allocated Error!\n");
        exit(0);
    }
    int mark = 1;
    printf("Check Heap\n");
    printf("Start: %p\n", mem_heap_lo());
    printf("End: %p\n", mem_heap_hi());
    int cnt = 0;
    char* boundaries = (char*)(mem_heap_hi());
    for (; bp != boundaries; bp = NEXT_BLKP(bp))
    {
        if (!aligned(bp))
        {
            printf("Aligned Error!\n");
            exit(0);
        }
        if (GET_SIZE(HDRP(bp)) == 0)
        {
            printf("EOL!\n");
            break;
        }
        if (lineno)
        {
            printf("Block %p with size %d\n", bp, GET_SIZE(HDRP(bp)));
            printf("State: ");
            if (GET_ALLOC(HDRP(bp)))
            {
                mark = 1;
                printf("Allocated\n");    
                printf("Header: %d\n", GET_SIZE(HDRP(bp)));            
            }
            else
            {
                printf("Free\n");
                if (mark == 0)
                {
                    printf("Consecutive Free Blocks Error!\n");
                    exit(0);
                }
                cnt ++;
                mark = 0;
                if (GET(HDRP(bp)) != GET(FTRP(bp)))
                {
                    printf("Header And Footer Match Error!\n");
                    exit(0);
                }
                printf("Header: %d\n", GET_SIZE(HDRP(bp)));
                printf("Footer: %d\n", GET_SIZE(FTRP(bp)));
            }
        }  
        
    }
    printf("Check Lists\n");
    printf("Now We Are Checking List01\n");
    int cnt1 = 0;
    if (l01 == NULL)
    {
        printf("List01 Is Empty\n");
    }
    else
    {
        size_t* startx = l01;
        for(; startx != NULL; startx = (size_t*)*startx)
        {
            cnt1 ++;
            if (!in_heap(startx))
            {
                printf("Block Out Of Range Error!\n");
                exit(0);
            }
            printf("The Current Block is %p with size %d", startx, GET_SIZE(HDRP(startx)));
            if (GET_SIZE(HDRP(startx)) > num01)
            {
                printf("Block Size Out Of Range Error!\n");
            }
        }
    }
    printf("Now We Are Checking List02\n");
    if (l02 == NULL)
    {
        printf("List02 Is Empty\n");
    }
    else
    {
        size_t* startx = l02;
        for(; startx != NULL; startx = (size_t*)*startx)
        {
            cnt1 ++;
            if (!in_heap(startx))
            {
                printf("Block Out Of Range Error!\n");
                exit(0);
            }
            printf("The Current Block is %p with size %d", startx, GET_SIZE(HDRP(startx)));
            if (GET_SIZE(HDRP(startx)) > num02)
            {
                printf("Block Size Out Of Range Error!\n");
            }
        }
    }
    printf("Now We Are Checking List03\n");
    if (l03 == NULL)
    {
        printf("List03 Is Empty\n");
    }
    else
    {
        size_t* startx = l03;
        for(; startx != NULL; startx = (size_t*)*startx)
        {
            cnt1 ++;
            if (!in_heap(startx))
            {
                printf("Block Out Of Range Error!\n");
                exit(0);
            }
            printf("The Current Block is %p with size %d", startx, GET_SIZE(HDRP(startx)));
            if (GET_SIZE(HDRP(startx)) > num03)
            {
                printf("Block Size Out Of Range Error!\n");
            }
        }
    }
    printf("Now We Are Checking List04\n");
    if (l04 == NULL)
    {
        printf("List01 Is Empty\n");
    }
    else
    {
        size_t* startx = l04;
        for(; startx != NULL; startx = (size_t*)*startx)
        {
            cnt1 ++;
            if (!in_heap(startx))
            {
                printf("Block Out Of Range Error!\n");
                exit(0);
            }
            printf("The Current Block is %p with size %d", startx, GET_SIZE(HDRP(startx)));
            if (GET_SIZE(HDRP(startx)) > num04)
            {
                printf("Block Size Out Of Range Error!\n");
            }
        }
    }
    printf("Now We Are Checking List05\n");
    if (l05 == NULL)
    {
        printf("List05 Is Empty\n");
    }
    else
    {
        size_t* startx = l05;
        for(; startx != NULL; startx = (size_t*)*startx)
        {
            cnt1 ++;
            if (!in_heap(startx))
            {
                printf("Block Out Of Range Error!\n");
                exit(0);
            }
            printf("The Current Block Is %p With Size %d\n", startx, GET_SIZE(HDRP(startx)));
            if (GET_SIZE(HDRP(startx)) > num05)
            {
                printf("Block Size Out Of Range Error!\n");
            }
        }
    }
    printf("Now We Are Checking List06\n");
    if (l06 == NULL)
    {
        printf("List06 Is Empty\n");
    }
    else
    {
        size_t* startx = l06;
        for(; startx != NULL; startx = (size_t*)*startx)
        {
            cnt1 ++;
            if (!in_heap(startx))
            {
                printf("Block Out Of Range Error!\n");
                exit(0);
            }
            printf("The Current Block Is %p With Size %d\n", startx, GET_SIZE(HDRP(startx)));
            if (GET_SIZE(HDRP(startx)) > num06)
            {
                printf("Block Size Out Of Range Error!\n");
            }
        }
    }
    printf("Now We Are Checking List07\n");
    if (l07 == NULL)
    {
        printf("List07 Is Empty\n");
    }
    else
    {
        size_t* startx = l07;
        for(; startx != NULL; startx = (size_t*)*startx)
        {
            cnt1 ++;
            if (!in_heap(startx))
            {
                printf("Block Out Of Range Error!\n");
                exit(0);
            }
            printf("The Current Block Is %p With Size %d\n", startx, GET_SIZE(HDRP(startx)));
            if (GET_SIZE(HDRP(startx)) > num07)
            {
                printf("Block Size Out Of Range Error!\n");
            }
        }
    }
    printf("Now We Are Checking List08\n");
    if (l08 == NULL)
    {
        printf("List08 Is Empty\n");
    }
    else
    {
        size_t* startx = l08;
        for(; startx != NULL; startx = (size_t*)*startx)
        {
            cnt1 ++;
            if (!in_heap(startx))
            {
                printf("Block Out Of Range Error!\n");
                exit(0);
            }
            printf("The Current Block Is %p With Size %d\n", startx, GET_SIZE(HDRP(startx)));
            if (GET_SIZE(HDRP(startx)) > num08)
            {
                printf("Block Size Out Of Range Error!\n");
            }
        }
    }
    printf("Now We Are Checking List09\n");
    if (l09 == NULL)
    {
        printf("List09 Is Empty\n");
    }
    else
    {
        size_t* startx = l09;
        for(; startx != NULL; startx = (size_t*)*startx)
        {
            cnt1 ++;
            if (!in_heap(startx))
            {
                printf("Block Out Of Range Error!\n");
                exit(0);
            }
            printf("The Current Block Is %p With Size %d\n", startx, GET_SIZE(HDRP(startx)));
            if (GET_SIZE(HDRP(startx)) > num09)
            {
                printf("Block Size Out Of Range Error!\n");
            }
        }
    }
    printf("Now We Are Checking List10\n");
    if (l10 == NULL)
    {
        printf("List10 Is Empty\n");
    }
    else
    {
        size_t* startx = l10;
        for(; startx != NULL; startx = (size_t*)*startx)
        {
            cnt1 ++;
            if (!in_heap(startx))
            {
                printf("Block Out Of Range Error!\n");
                exit(0);
            }
            printf("The Current Block Is %p With Size %d\n", startx, GET_SIZE(HDRP(startx)));
            if (GET_SIZE(HDRP(startx)) > num10)
            {
                printf("Block Size Out Of Range Error!\n");
            }
        }
    }
    printf("Now We Are Checking List11\n");
    if (l11 == NULL)
    {
        printf("List11 Is Empty\n");
    }
    else
    {
        size_t* startx = l11;
        for(; startx != NULL; startx = (size_t*)*startx)
        {
            cnt1 ++;
            if (!in_heap(startx))
            {
                printf("Block Out Of Range Error!\n");
                exit(0);
            }
            printf("The Current Block Is %p With Size %d\n", startx, GET_SIZE(HDRP(startx)));
            if (GET_SIZE(HDRP(startx)) > num11)
            {
                printf("Block Size Out Of Range Error!\n");
            }
        }
    }
    printf("Now We Are Checking List12\n");
    if (l12 == NULL)
    {
        printf("List12 Is Empty\n");
    }
    else
    {
        size_t* startx = l12;
        for(; startx != NULL; startx = (size_t*)*startx)
        {
            cnt1 ++;
            if (!in_heap(startx))
            {
                printf("Block Out Of Range Error!\n");
                exit(0);
            }
            printf("The Current Block Is %p With Size %d\n", startx, GET_SIZE(HDRP(startx)));
            if (GET_SIZE(HDRP(startx)) > num12)
            {
                printf("Block Size Out Of Range Error!\n");
            }
        }
    }
    printf("Now We Are Checking List13\n");
    if (l13 == NULL)
    {
        printf("List13 Is Empty\n");
    }
    else
    {
        size_t* startx = l13;
        for(; startx != NULL; startx = (size_t*)*startx)
        {
            cnt1 ++;
            if (!in_heap(startx))
            {
                printf("Block Out Of Range Error!\n");
                exit(0);
            }
            printf("The Current Block Is %p With Size %d\n", startx, GET_SIZE(HDRP(startx)));
            if (GET_SIZE(HDRP(startx)) > num13)
            {
                printf("Block Size Out Of Range Error!\n");
            }
        }
    }
    printf("Now We Are Checking List14\n");
    if (l14 == NULL)
    {
        printf("List14 Is Empty\n");
    }
    else
    {
        size_t* startx = l14;
        for(; startx != NULL; startx = (size_t*)*startx)
        {
            cnt1 ++;
            if (!in_heap(startx))
            {
                printf("Block Out Of Range Error!\n");
                exit(0);
            }
            printf("The Current Block Is %p With Size %d\n", startx, GET_SIZE(HDRP(startx)));
            if (GET_SIZE(HDRP(startx)) > num14)
            {
                printf("Block Size Out Of Range Error!\n");
            }
        }
    }
    printf("Now We Are Checking List15\n");
    if (l15 == NULL)
    {
        printf("List15 Is Empty\n");
    }
    else
    {
        size_t* startx = l15;
        for(; startx != NULL; startx = (size_t*)*startx)
        {
            cnt1 ++;
            if (!in_heap(startx))
            {
                printf("Block Out Of Range Error!\n");
                exit(0);
            }
            printf("The Current Block Is %p With Size %d\n", startx, GET_SIZE(HDRP(startx)));
            if (GET_SIZE(HDRP(startx)) <= num14)
            {
                printf("Block Size Out Of Range Error!\n");
            }
        }
    }
    printf("Free Blocks Number Is %d\n", cnt);
    if (cnt != cnt1)
    {
        printf("Free Blocks Numbers Match Error!\n");
        exit(0);
    }
}

/* 
 * extend_heap - Extend heap with free block and return its block pointer
 */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;
    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    size_t checkprev = PREVX(HDRP(bp));
    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, checkprev, 0)); /* Free block header */
    PUT(FTRP(bp), PACK(size, checkprev, 0)); /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 0, 1)); /* New epilogue header */

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

/*
 * coalesce - Boundary tag coalescing. Return ptr to coalesced block
 */
static void *coalesce(void *bp)
{
    /* check the previous block and the next block normally */
    size_t prev_alloc = PREVX(HDRP(bp));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    /* if prev_alloc == 4, the previous block is allocated */
    if ((prev_alloc == 4) && next_alloc) /* Case 1 */
    { 
        insertx(bp, size);
        return bp;
    }
    else if ((prev_alloc == 4) && !next_alloc) /* Case 2 */
    {
        size_t k = GET_SIZE(HDRP(NEXT_BLKP(bp)));
        deletex(NEXT_BLKP(bp), k);
        size += k;
        PUT(HDRP(bp), PACK(size, 4, 0));
        PUT(FTRP(bp), PACK(size, 4, 0));
        insertx(bp, size);
    }
    else if ((prev_alloc != 4) && next_alloc)  /* Case 3 */
    {                                        
        size_t k = GET_SIZE(HDRP(PREV_BLKP(bp)));
        deletex(PREV_BLKP(bp), k);
        size += k;
        PUT(FTRP(bp), PACK(size, 4, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 4, 0));
        bp = PREV_BLKP(bp);
        insertx(bp, size);
    }
    else
    {                                              /* Case 4 */
        size_t t1 = GET_SIZE(HDRP(PREV_BLKP(bp))); 
        size_t t2 = GET_SIZE(FTRP(NEXT_BLKP(bp)));
        deletex(PREV_BLKP(bp), t1);
        deletex(NEXT_BLKP(bp), t2);
        size += t1 + t2;
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 4, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 4, 0));
        bp = PREV_BLKP(bp);
        insertx(bp, size);
    }
    return bp;
}

/* 
 * place - Place block of asize bytes at start of free block bp 
 *         and split if remainder would be at least minimum block size
 */
static void* place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    size_t checkprev = PREVX(HDRP(bp));
    deletex(bp, asize);
    if ((csize - asize) >= (2 * DSIZE))
    {
        if (asize < 120) 
        /* the if the size is small, using the theory of the probability 
         * theory, the previous blocks are likely to be small in a 
         * real-in-use engineering program.
         */
        {
            PUT(HDRP(bp), PACK(asize, checkprev, 1));
            char* xxx = NEXT_BLKP(bp); 
            PUT(HDRP(xxx), PACK(csize - asize, 4, 0));
            PUT(FTRP(xxx), PACK(csize - asize, 4, 0));
            insertx(xxx, csize - asize);
            return bp;
        }
        else
        {
            PUT(HDRP(bp), PACK(csize - asize, checkprev, 0));
            PUT(FTRP(bp), PACK(csize - asize, checkprev, 0));
            insertx(bp, csize - asize);
            bp = NEXT_BLKP(bp);  
            PUT(HDRP(bp), PACK(asize, 0, 1));
            /* change the status of the next block of the next block */
            PUT(HDRP(NEXT_BLKP(bp)), PACK(GET_SIZE(HDRP(NEXT_BLKP(bp))), 4, GET_ALLOC(HDRP(NEXT_BLKP(bp)))));
            if (GET_ALLOC(HDRP(NEXT_BLKP(bp))) == 0)
            {
                PUT(FTRP(NEXT_BLKP(bp)), PACK(GET_SIZE(HDRP(NEXT_BLKP(bp))), 4, GET_ALLOC(HDRP(NEXT_BLKP(bp)))));
            }
            /* change the returned bp--pointing to the head of the malloced place */
            return bp;
        }
    }
    else
    {
        PUT(HDRP(bp), PACK(csize, checkprev, 1));
        PUT(FTRP(bp), PACK(csize, checkprev, 1));
        /* change the status of the next block of the next block */
        PUT(HDRP(NEXT_BLKP(bp)), PACK(GET_SIZE(HDRP(NEXT_BLKP(bp))), 4, GET_ALLOC(HDRP(NEXT_BLKP(bp)))));
        if (GET_ALLOC(HDRP(NEXT_BLKP(bp))) == 0)
        {
            PUT(FTRP(NEXT_BLKP(bp)), PACK(GET_SIZE(HDRP(NEXT_BLKP(bp))), 4, GET_ALLOC(HDRP(NEXT_BLKP(bp)))));
        }
        return bp;
    }
    return bp;
}

/* 
 * insertx - insert a block with fixed size to lists
 */
static void insertx(void *bp, size_t asize)
{
    /* check the size of the block to determine which list to manipulate */
    if (asize <= num01)
    {
        size_t *temp = (size_t *)(bp); //the head of the link list
        *temp = (size_t)l01;
        l01 = bp;
        return;
    }
    if (asize <= num02)
    {
        size_t *temp = (size_t *)(bp); //the head of the link list
        *temp = (size_t)l02;
        l02 = bp;
        return;
    }
    if (asize <= num03)
    {
        size_t *temp = (size_t *)(bp); //the head of the link list
        *temp = (size_t)l03;
        l03 = bp;
        return;
    }
    if (asize == num04)
    {
        size_t *temp = (size_t *)(bp); //the head of the link list
        *temp = (size_t)l04;
        l04 = bp;
        return;
    }
    if (asize == num05)
    {
        size_t *temp = (size_t *)(bp); //the head of the link list
        *temp = (size_t)l05;
        l05 = bp;
        return;
    }
    if (asize <= num06)
    {
        size_t *temp = (size_t *)(bp); //the head of the link list
        *temp = (size_t)l06;
        l06 = bp;
        return;
    }
    if (asize <= num07)
    {
        size_t *temp = (size_t *)(bp); //the head of the link list
        *temp = (size_t)l07;
        l07 = bp;
        return;
    }
    if (asize <= num08)
    {
        size_t *temp = (size_t *)(bp); //the head of the link list
        *temp = (size_t)l08;
        l08 = bp;
        return;
    }
    if (asize <= num09)
    {
        size_t *temp = (size_t *)(bp); //the head of the link list
        *temp = (size_t)l09;
        l09 = bp;
        return;
    }
    if (asize <= num10)
    {
        size_t *temp = (size_t *)(bp); //the head of the link list
        *temp = (size_t)l10;
        l10 = bp;
        return;
    }
    if (asize <= num11)
    {
        size_t *temp = (size_t *)(bp); //the head of the link list
        *temp = (size_t)l11;
        l11 = bp;
        return;
    }
    if (asize <= num12)
    {
        size_t *temp = (size_t *)(bp); //the head of the link list
        *temp = (size_t)l12;
        l12 = bp;
        return;
    }
    if (asize <= num13)
    {
        size_t *temp = (size_t *)(bp); //the head of the link list
        *temp = (size_t)l13;
        l13 = bp;
        return;
    }
    if (asize <= num14)
    {
        size_t *temp = (size_t *)(bp); //the head of the link list
        *temp = (size_t)l14;
        l14 = bp;
        return;
    }
    size_t *temp = (size_t *)(bp); //the head of the link list
    *temp = (size_t)l15;
    l15 = bp;
    return;
}

/* 
 * deletex - delete a block with fixed size in lists
 */
static void deletex(void *bp, size_t asize)
{
    size_t *nowbp = (size_t *)bp;
    size_t *nextk = (size_t *)(*nowbp);
    /* find the list that contains the block based on the block size */
    if (asize <= num01)
    {
        size_t *nowx = l01;
        if (l01 == bp)
        {
            if (nextk != NULL)
            {
                l01 = nextk;
                return;
            }
            l01 = NULL;
            return;
        }
        while (nowx)
        {
            if ((size_t)*nowx == (size_t)nowbp)
            {
                *nowx = (size_t)(nextk);
                return;
            }
            else
            {
                nowx = (size_t *)*nowx;
            }
        }
    }
    if (asize <= num02)
    {
        size_t *nowx = l02;
        if (l02 == bp)
        {
            if (nextk != NULL)
            {
                l02 = nextk;
                return;
            }
            l02 = NULL;
            return;
        }
        while (nowx)
        {
            if ((size_t)*nowx == (size_t)nowbp)
            {
                *nowx = (size_t)(nextk);
                return;
            }
            else
            {
                nowx = (size_t *)*nowx;
            }
        }
    }
    if (asize <= num03)
    {
        size_t *nowx = l03;
        if (l03 == bp)
        {
            if (nextk != NULL)
            {
                l03 = nextk;
                return;
            }
            l03 = NULL;
            return;
        }
        while (nowx)
        {
            if ((size_t)*nowx == (size_t)nowbp)
            {
                *nowx = (size_t)(nextk);
                return;
            }
            else
            {
                nowx = (size_t *)*nowx;
            }
        }
    }
    if (asize == num04)
    {
        size_t *nowx = l04;
        if (l04 == bp)
        {
            if (nextk != NULL)
            {
                l04 = nextk;
                return;
            }
            l04 = NULL;
            return;
        }
        while (nowx)
        {
            if ((size_t)*nowx == (size_t)nowbp)
            {
                *nowx = (size_t)(nextk);
                return;
            }
            else
            {
                nowx = (size_t *)*nowx;
            }
        }
    }
    if (asize == num05)
    {
        size_t *nowx = l05;
        if (l05 == bp)
        {
            if (nextk != NULL)
            {
                l05 = nextk;
                return;
            }
            l05 = NULL;
            return;
        }
        while (nowx)
        {
            if ((size_t)*nowx == (size_t)nowbp)
            {
                *nowx = (size_t)(nextk);
                return;
            }
            else
            {
                nowx = (size_t *)*nowx;
            }
        }
    }
    if (asize <= num06)
    {
        size_t *nowx = l06;
        if (l06 == bp)
        {
            if (nextk != NULL)
            {
                l06 = nextk;
                return;
            }
            l06 = NULL;
            return;
        }
        while (nowx)
        {
            if ((size_t)*nowx == (size_t)nowbp)
            {
                *nowx = (size_t)(nextk);
                return;
            }
            else
            {
                nowx = (size_t *)*nowx;
            }
        }
    }
    if (asize <= num07)
    {
        size_t *nowx = l07;
        if (l07 == bp)
        {
            if (nextk != NULL)
            {
                l07 = nextk;
                return;
            }
            l07 = NULL;
            return;
        }
        while (nowx)
        {
            if ((size_t)*nowx == (size_t)nowbp)
            {
                *nowx = (size_t)(nextk);
                return;
            }
            else
            {
                nowx = (size_t *)*nowx;
            }
        }
    }
    if (asize <= num08)
    {
        size_t *nowx = l08;
        if (l08 == bp)
        {
            if (nextk != NULL)
            {
                l08 = nextk;
                return;
            }
            l08 = NULL;
            return;
        }
        while (nowx)
        {
            if ((size_t)*nowx == (size_t)nowbp)
            {
                *nowx = (size_t)(nextk);
                return;
            }
            else
            {
                nowx = (size_t *)*nowx;
            }
        }
    }
    if (asize <= num09)
    {
        size_t *nowx = l09;
        if (l09 == bp)
        {
            if (nextk != NULL)
            {
                l09 = nextk;
                return;
            }
            l09 = NULL;
            return;
        }
        while (nowx)
        {
            if ((size_t)*nowx == (size_t)nowbp)
            {
                *nowx = (size_t)(nextk);
                return;
            }
            else
            {
                nowx = (size_t *)*nowx;
            }
        }
    }
    if (asize <= num10)
    {
        size_t *nowx = l10;
        if (l10 == bp)
        {
            if (nextk != NULL)
            {
                l10 = nextk;
                return;
            }
            l10 = NULL;
            return;
        }
        while (nowx)
        {
            if ((size_t)*nowx == (size_t)nowbp)
            {
                *nowx = (size_t)(nextk);
                return;
            }
            else
            {
                nowx = (size_t *)*nowx;
            }
        }
    }
    if (asize <= num11)
    {
        size_t *nowx = l11;
        if (l11 == bp)
        {
            if (nextk != NULL)
            {
                l11 = nextk;
                return;
            }
            l11 = NULL;
            return;
        }
        while (nowx)
        {
            if ((size_t)*nowx == (size_t)nowbp)
            {
                *nowx = (size_t)(nextk);
                return;
            }
            else
            {
                nowx = (size_t *)*nowx;
            }
        }
    }
    if (asize <= num12)
    {
        size_t *nowx = l12;
        if (l12 == bp)
        {
            if (nextk != NULL)
            {
                l12 = nextk;
                return;
            }
            l12 = NULL;
            return;
        }
        while (nowx)
        {
            if ((size_t)*nowx == (size_t)nowbp)
            {
                *nowx = (size_t)(nextk);
                return;
            }
            else
            {
                nowx = (size_t *)*nowx;
            }
        }
    }
    if (asize <= num13)
    {
        size_t *nowx = l13;
        if (l13 == bp)
        {
            if (nextk != NULL)
            {
                l13 = nextk;
                return;
            }
            l13 = NULL;
            return;
        }
        while (nowx)
        {
            if ((size_t)*nowx == (size_t)nowbp)
            {
                *nowx = (size_t)(nextk);
                return;
            }
            else
            {
                nowx = (size_t *)*nowx;
            }
        }
    }
    if (asize <= num14)
    {
        size_t *nowx = l14;
        if (l14 == bp)
        {
            if (nextk != NULL)
            {
                l14 = nextk;
                return;
            }
            l14 = NULL;
            return;
        }
        while (nowx)
        {
            if ((size_t)*nowx == (size_t)nowbp)
            {
                *nowx = (size_t)(nextk);
                return;
            }
            else
            {
                nowx = (size_t *)*nowx;
            }
        }
    }
    size_t *nowx = l15;
    if (l15 == bp)
    {
        if (nextk != NULL)
        {
            l15 = nextk;
            return;
        }
        l15 = NULL;
        return;
    }
    while (nowx)
    {
        if ((size_t)*nowx == (size_t)nowbp)
        {
            *nowx = (size_t)(nextk);
            return;
        }
        else
        {
            nowx = (size_t *)*nowx;
        }
    }
    return;
}

/* 
 * find_fit - Find a fit for a block with asize bytes 
 * search in the lists one by one.
 */
static void *find_fit(size_t asize)
{
    size_t *bp = l01;
    size_t *now_list_start = bp;
    /* find the block in the lists */
    if (asize <= num01)
    {
        /* iterate in the list */
        if (now_list_start != NULL)
        {
            while (now_list_start)
            {
                if ((GET_SIZE(HDRP(now_list_start))) >= asize)
                {
                    bp = now_list_start;
                    return bp;
                }
                else
                {
                    if (*now_list_start != (size_t)NULL)
                    {
                        now_list_start = (size_t *)*(now_list_start);
                    }
                    else
                    {
                        break;
                    }
                }
            }
        }
    }
    if (asize <= num02)
    {
        size_t *bp = l02;
        size_t *now_list_start = bp;
        if (now_list_start != NULL)
        {
            while (now_list_start)
            {
                if ((GET_SIZE(HDRP(now_list_start))) >= asize)
                {
                    bp = now_list_start;
                    return bp;
                }
                else
                {
                    if (*now_list_start != (size_t)NULL)
                    {
                        now_list_start = (size_t *)*(now_list_start);
                    }
                    else
                    {
                        break;
                    }
                }
            }
        }
    }
    if (asize <= num03)
    {
        size_t *bp = l03;
        size_t *now_list_start = bp;
        if (now_list_start != NULL)
        {
            while (now_list_start)
            {
                if ((GET_SIZE(HDRP(now_list_start))) >= asize)
                {
                    bp = now_list_start;
                    return bp;
                }
                else
                {
                    if (*now_list_start != (size_t)NULL)
                    {
                        now_list_start = (size_t *)*(now_list_start);
                    }
                    else
                    {
                        break;
                    }
                }
            }
        }
    }
    if (asize == num04)
    {
        size_t *bp = l04;
        size_t *now_list_start = bp;
        if (now_list_start != NULL)
        {
            while (now_list_start)
            {
                if ((GET_SIZE(HDRP(now_list_start))) >= asize)
                {
                    bp = now_list_start;
                    return bp;
                }
                else
                {
                    if (*now_list_start != (size_t)NULL)
                    {
                        now_list_start = (size_t *)*(now_list_start);
                    }
                    else
                    {
                        break;
                    }
                }
            }
        }
    }
    if (asize == num05)
    {
        size_t *bp = l05;
        size_t *now_list_start = bp;
        if (now_list_start != NULL)
        {
            while (now_list_start)
            {
                if ((GET_SIZE(HDRP(now_list_start))) >= asize)
                {
                    bp = now_list_start;
                    return bp;
                }
                else
                {
                    if (*now_list_start != (size_t)NULL)
                    {
                        now_list_start = (size_t *)*(now_list_start);
                    }
                    else
                    {
                        break;
                    }
                }
            }
        }
    }
    if (asize <= num06)
    {
        size_t *bp = l06;
        size_t *now_list_start = bp;
        if (now_list_start != NULL)
        {
            while (now_list_start)
            {
                if ((GET_SIZE(HDRP(now_list_start))) >= asize)
                {
                    bp = now_list_start;
                    return bp;
                }
                else
                {
                    if (*now_list_start != (size_t)NULL)
                    {
                        now_list_start = (size_t *)*(now_list_start);
                    }
                    else
                    {
                        break;
                    }
                }
            }
        }
    }
    if (asize <= num07)
    {
        size_t *bp = l07;
        size_t *now_list_start = bp;
        if (now_list_start != NULL)
        {
            while (now_list_start)
            {
                if ((GET_SIZE(HDRP(now_list_start))) >= asize)
                {
                    bp = now_list_start;
                    return bp;
                }
                else
                {
                    if (*now_list_start != (size_t)NULL)
                    {
                        now_list_start = (size_t *)*(now_list_start);
                    }
                    else
                    {
                        break;
                    }
                }
            }
        }
    }
    if (asize <= num08)
    {
        size_t *bp = l08;
        size_t *now_list_start = bp;
        if (now_list_start != NULL)
        {
            while (now_list_start)
            {
                if ((GET_SIZE(HDRP(now_list_start))) >= asize)
                {
                    bp = now_list_start;
                    return bp;
                }
                else
                {
                    if (*now_list_start != (size_t)NULL)
                    {
                        now_list_start = (size_t *)*(now_list_start);
                    }
                    else
                    {
                        break;
                    }
                }
            }
        }
    }
    if (asize <= num09)
    {
        size_t *bp = l09;
        size_t *now_list_start = bp;
        if (now_list_start != NULL)
        {
            while (now_list_start)
            {
                if ((GET_SIZE(HDRP(now_list_start))) >= asize)
                {
                    bp = now_list_start;
                    return bp;
                }
                else
                {
                    if (*now_list_start != (size_t)NULL)
                    {
                        now_list_start = (size_t *)*(now_list_start);
                    }
                    else
                    {
                        break;
                    }
                }
            }
        }
    }
    if (asize <= num10)
    {
        size_t *bp = l10;
        size_t *now_list_start = bp;
        if (now_list_start != NULL)
        {
            while (now_list_start)
            {
                if ((GET_SIZE(HDRP(now_list_start))) >= asize)
                {
                    bp = now_list_start;
                    return bp;
                }
                else
                {
                    if (*now_list_start != (size_t)NULL)
                    {
                        now_list_start = (size_t *)*(now_list_start);
                    }
                    else
                    {
                        break;
                    }
                }
            }
        }
    }
    if (asize <= num11)
    {
        size_t *bp = l11;
        size_t *now_list_start = bp;
        if (now_list_start != NULL)
        {
            while (now_list_start)
            {
                if ((GET_SIZE(HDRP(now_list_start))) >= asize)
                {
                    bp = now_list_start;
                    return bp;
                }
                else
                {
                    if (*now_list_start != (size_t)NULL)
                    {
                        now_list_start = (size_t *)*(now_list_start);
                    }
                    else
                    {
                        break;
                    }
                }
            }
        }
    }
    if (asize <= num12)
    {
        size_t *bp = l12;
        size_t *now_list_start = bp;
        if (now_list_start != NULL)
        {
            while (now_list_start)
            {
                if ((GET_SIZE(HDRP(now_list_start))) >= asize)
                {
                    bp = now_list_start;
                    return bp;
                }
                else
                {
                    if (*now_list_start != (size_t)NULL)
                    {
                        now_list_start = (size_t *)*(now_list_start);
                    }
                    else
                    {
                        break;
                    }
                }
            }
        }
    }
    if (asize <= num13)
    {
        size_t *bp = l13;
        size_t *now_list_start = bp;
        if (now_list_start != NULL)
        {
            while (now_list_start)
            {
                if ((GET_SIZE(HDRP(now_list_start))) >= asize)
                {
                    bp = now_list_start;
                    return bp;
                }
                else
                {
                    if (*now_list_start != (size_t)NULL)
                    {
                        now_list_start = (size_t *)*(now_list_start);
                    }
                    else
                    {
                        break;
                    }
                }
            }
        }
    }
    if (asize <= num14)
    {
        size_t *bp = l14;
        size_t *now_list_start = bp;
        if (now_list_start != NULL)
        {
            while (now_list_start)
            {
                if ((GET_SIZE(HDRP(now_list_start))) >= asize)
                {
                    bp = now_list_start;
                    return bp;
                }
                else
                {
                    if (*now_list_start != (size_t)NULL)
                    {
                        now_list_start = (size_t *)*(now_list_start);
                    }
                    else
                    {
                        break;
                    }
                }
            }
        }
    }
    bp = l15;
    now_list_start = bp;
    if (bp == NULL)
    {
        /* if the last list does not contain elements, return NULL */
        return NULL;
    }
    while (now_list_start)
    {
        if ((GET_SIZE(HDRP(now_list_start))) >= asize)
        {
            bp = now_list_start;
            return bp;
        }
        else
        {
            if (*now_list_start != (size_t)NULL)
            {
                now_list_start = (size_t *)*(now_list_start);
            }
            else
            {
                return NULL;
            }
        }
    }
    return NULL;
}
