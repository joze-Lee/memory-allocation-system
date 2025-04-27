#include <stdbool.h>
#include <assert.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"
#include "config.h"

#include "list.h"

team_t team = {
    "Ani & Abi",
    "Anirudh Kurma",
    "anirudhk313@vt.edu",
    "Abilash Pradeep",
    "abilashp@vt.edu",
};

struct boundary_tag
{
    int inuse : 1; // inuse bit
    int size : 31; // size of block, in words
                   // block size
};

/* FENCE is used for heap prologue/epilogue. */
const struct boundary_tag FENCE = {
    .inuse = 1,
    .size = 0};

/* A C struct describing the beginning of each block.
 *
 * If each block is aligned at 12 mod 16, each payload will
 * be aligned at 0 mod 16.
 */
struct block
{
    struct boundary_tag header; /* offset 0, at address 12 mod 16 */
    char payload[0];            /* offset 4, at address 0 mod 16 */
};

struct free_block
{
    struct boundary_tag header;
    struct list_elem elem;

    char payload[0];
};

/* Basic constants and macros */
#define WSIZE sizeof(struct boundary_tag) /* Word and header/footer size (bytes) */
#define MIN_BLOCK_SIZE_WORDS 8            /* Minimum block size in words */
#define CHUNKSIZE (1 << 10)               /* Extend heap by this amount (words) */
static size_t chunkSize;

static inline size_t max(size_t x, size_t y)
{
    return x > y ? x : y;
}

static size_t align(size_t size)
{
    return (size + ALIGNMENT - 1) & ~(ALIGNMENT - 1);
}

static bool is_aligned(size_t size) __attribute__((__unused__));
static bool is_aligned(size_t size)
{
    return size % ALIGNMENT == 0;
}

/* Global variables */
static struct list FreeList[19];

/* Function prototypes for internal helper routines */
static struct block *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static struct block *find_fit(size_t asize);
static struct block *coalesce(void *block);

int getFreeListIndex(int size)
{
    if (size <= 16)
    {

        if (size <= 2)
        {
            return 0;
        }
        else if (size == 3)
        {
            return 1;
        }
        else if (size == 4)
        {
            return 2;
        }
        else if (size == 5)
        {
            return 3;
        }
        else if (size == 6)
        {
            return 4;
        }
        else if (size == 7)
        {
            return 5;
        }
        else if (size == 8)
        {
            return 6;
        }
        else if (size <= 10)
        {
            return 7;
        }
        else if (size <= 12)
        {
            return 8;
        }
        else if (size <= 14)
        {
            return 9;
        }
        else
        {
            return 10;
        }
    }
    else
    {
        if (size <= 32)
        {
            return 11;
        }
        else if (size <= 64)
        {
            return 12;
        }
        else if (size <= 128)
        {
            return 13;
        }
        else if (size <= 256)
        {
            return 14;
        }
        else if (size <= 512)
        {
            return 15;
        }
        else if (size <= 1024)
        {
            return 16;
        }
        else if (size <= 2048)
        {
            return 17;
        }
        else
        {
            return 18;
        }
    }
}

void removeFreeList(struct free_block *blk)
{
    list_remove(&blk->elem);
}
void addFreeList(struct free_block *blk)
{
    // printf("addFreeList %p %p %li, %li \n", blk, &blk->elem, sizeof(struct free_block), MIN_BLOCK_SIZE_WORDS*WSIZE);
    list_push_back(&FreeList[getFreeListIndex(blk->header.size)], &blk->elem);
}

/* Given a block, obtain previous's block footer.
   Works for left-most block also. */
static struct boundary_tag *prev_blk_footer(struct block *blk) // Ok
{
    return &blk->header - 1;
}

/* Return if block is free */
static bool blk_free(struct block *blk) // Ok
{
    return !blk->header.inuse;
}

/* Return size of block is free */
static size_t blk_size(struct block *blk) // Ok
{
    return blk->header.size;
}

/* Given a block, obtain pointer to previous block.
   Not meaningful for left-most block. */
static struct block *prev_blk(struct block *blk) // Ok
{
    struct boundary_tag *prevfooter = prev_blk_footer(blk);
    assert(prevfooter->size != 0);
    return (struct block *)((void *)blk - WSIZE * prevfooter->size);
}

/* Given a block, obtain pointer to next block.
   Not meaningful for right-most block. */
static struct block *next_blk(struct block *blk) // Ok
{
    assert(blk_size(blk) != 0);
    return (struct block *)((void *)blk + WSIZE * blk->header.size);
}

/* Given a block, obtain its footer boundary tag */
static struct boundary_tag *get_footer(struct block *blk) // Ok
{
    return ((void *)blk + WSIZE * blk->header.size) - sizeof(struct boundary_tag);
}

/* Set a block's size and inuse bit in header and footer */
static void set_header_and_footer(struct block *blk, int size, int inuse) // Ok
{
    blk->header.inuse = inuse;
    blk->header.size = size;
    *get_footer(blk) = blk->header; /* Copy header to footer */
}

/* Mark a block as used and set its size. */
static void mark_block_used(void *blk, int size) // Ok
{
    // printf("mark_block_used %p %i  \n", blk, size);

    set_header_and_footer(blk, size, 1);
    removeFreeList(blk);
}

/* Mark a block as free and set its size. */
static void mark_block_free(void *blk, int size) // Ok
{
    // printf("mark_block_free %p %i  \n", blk, size);

    set_header_and_footer(blk, size, 0);
    addFreeList(blk);
}

/*
 * mm_init - Initialize the memory manager
 */
int mm_init(void)
{
    // printf("Enering mm_init() \n");

    assert(offsetof(struct block, payload) == 4);
    assert(sizeof(struct boundary_tag) == 4);

    /* Create the initial empty heap */
    struct boundary_tag *initial = mem_sbrk(4 * sizeof(struct boundary_tag));
    if (initial == NULL)
        return -1;

    for (int i = 0; i < 19; i++)
    {
        list_init(&FreeList[i]);
    }

    chunkSize = mem_pagesize();
    chunkSize = CHUNKSIZE / 4;

    /* We use a slightly different strategy than suggested in the book.
     * Rather than placing a min-sized prologue block at the beginning
     * of the heap, we simply place two fences.
     * The consequence is that coalesce() must call prev_blk_footer()
     * and not prev_blk() because prev_blk() cannot be called on the
     * left-most block.
     */
    initial[2] = FENCE; /* Prologue footer */
    // heap_listp = (struct block *)&initial[3];
    initial[3] = FENCE; /* Epilogue header */

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(chunkSize) == NULL)
        return -1;

    // printf("Exiting mm_init() \n");

    return 0;
}

/*
 * mm_malloc - Allocate a block with at least size bytes of payload
 */
void *mm_malloc(size_t size)
{
    // printf("Entering mm_malloc(%li) \n", size);

    struct block *bp;

    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    size_t bsize = align(size + 2 * sizeof(struct boundary_tag)); /* account for tags */
    if (bsize < size)
        return NULL; /* integer overflow */

    /* Adjusted block size in words */
    size_t awords = max(MIN_BLOCK_SIZE_WORDS, bsize / WSIZE); /* respect minimum size */

    /* Search the free list for a fit */
    if ((bp = find_fit(awords)) != NULL)
    {
        // printf("Placing %li at %p \n", awords, bp);
        place(bp, awords);

        // printf("Exiting mm_malloc(%li) \n", size);
        // printf("Placed %i %i at %p \n", bp->header.size, bp->header.inuse, bp);

        return bp->payload;
    }

    // printf("Extending \n");

    /* No fit found. Get more memory and place the block */
    size_t extendwords = max(awords, chunkSize); /* Amount to extend heap if no fit */
    if ((bp = extend_heap(extendwords)) == NULL)
        return NULL;

    // printf("Placing %li at %p \n", awords, bp);
    place(bp, awords);
    // printf("Placed %i %i at %p \n", bp->header.size, bp->header.inuse, bp);

    // printf("Exiting mm_malloc(%li) \n", size);

    return bp->payload;
}

/*
 * mm_free - Free a block
 */
void mm_free(void *bp)
{
    if (bp == 0)
        return;

    /* Find block from user pointer */
    struct block *blk = bp - offsetof(struct block, payload);

    // printf("mm_free %i \n", blk->header.size);

    mark_block_free(blk, blk_size(blk));
    coalesce(blk);
}

/*
 * mm_realloc - Naive implementation of realloc
 */
void *mm_realloc(void *ptr, size_t size)
{
    // printf("mm_realloc %p \n", ptr);

    /* If size == 0 then this is just free, and we return NULL. */
    if (size == 0)
    {
        mm_free(ptr);
        return 0;
    }

    /* If oldptr is NULL, then this is just malloc. */
    if (ptr == NULL)
    {
        return mm_malloc(size);
    }

    struct block *block = ptr - offsetof(struct block, payload);
    size_t curSize = blk_size(block) * WSIZE - 2 * sizeof(struct boundary_tag);

    if (curSize > size)
    {

        char tmp[30];
        memcpy(tmp, ptr, 24);

        mark_block_free(block, blk_size(block));

        /* Adjust block size to include overhead and alignment reqs. */
        size_t bsize = align(size + 2 * sizeof(struct boundary_tag)); /* account for tags */
        if (bsize < size)
            return NULL; /* integer overflow */

        /* Adjusted block size in words */
        size_t awords = max(MIN_BLOCK_SIZE_WORDS, bsize / WSIZE); /* respect minimum size */

        place(block, awords);

        struct block *nxtBlock = next_blk(block);
        if (blk_free(nxtBlock))
        {
            coalesce(nxtBlock);
        }

        memcpy(ptr, tmp, 24);

        return ptr;
    }

    struct block *nxtBlock = next_blk(block);
    if (blk_free(nxtBlock))
    {
        curSize = curSize + blk_size(nxtBlock) * WSIZE;
        if (curSize > size)
        {

            char tmp[30];
            memcpy(tmp, ptr, 24);

            mark_block_free(block, blk_size(block));
            coalesce(nxtBlock);

            /* Adjust block size to include overhead and alignment reqs. */
            size_t bsize = align(size + 2 * sizeof(struct boundary_tag)); /* account for tags */
            if (bsize < size)
                return NULL; /* integer overflow */

            /* Adjusted block size in words */
            size_t awords = max(MIN_BLOCK_SIZE_WORDS, bsize / WSIZE); /* respect minimum size */

            place(block, awords);

            struct block *nxtBlock = next_blk(block);
            if (blk_free(nxtBlock))
            {
                coalesce(nxtBlock);
            }

            memcpy(ptr, tmp, 24);

            return ptr;
        }
    }

    void *newptr = mm_malloc(size);

    /* If realloc() fails the original block is left untouched  */
    if (!newptr)
    {
        return 0;
    }

    /* Copy the old data. */
    struct block *oldblock = ptr - offsetof(struct block, payload);
    size_t oldpayloadsize = blk_size(oldblock) * WSIZE - 2 * sizeof(struct boundary_tag);
    if (size < oldpayloadsize)
        oldpayloadsize = size;
    memcpy(newptr, ptr, oldpayloadsize);

    /* Free the old block. */
    mm_free(ptr);

    return newptr;
}

/*
 * coalesce - Boundary tag coalescing. Return ptr to coalesced block
 */
static struct block *coalesce(void *block)
{

    bool prev_alloc = prev_blk_footer(block)->inuse; /* is previous block allocated? */
    bool next_alloc = !blk_free(next_blk(block));    /* is next block allocated? */
    size_t size = blk_size(block);

    if (prev_alloc && next_alloc)
    { /* Case 1 */
        // both are allocated, nothing to coalesce
        return block;
    }

    else if (prev_alloc && !next_alloc)
    { /* Case 2 */
        // combine this block and next block by extending it

        void *nxtBlk = next_blk(block);
        removeFreeList(nxtBlk);

        removeFreeList(block);

        mark_block_free(block, size + blk_size(nxtBlk));
    }

    else if (!prev_alloc && next_alloc)
    { /* Case 3 */
        // combine previous and this block by extending previous

        void *prevBlk = prev_blk(block);
        removeFreeList(prevBlk);

        removeFreeList(block);

        block = prevBlk;

        mark_block_free(block, size + blk_size(block));
    }

    else
    { /* Case 4 */
        // combine all previous, this, and next block into one

        void *prevBlk = prev_blk(block);
        removeFreeList(prevBlk);

        void *nxtBlk = next_blk(block);
        removeFreeList(nxtBlk);

        removeFreeList(block);

        mark_block_free(prevBlk,
                        size + blk_size(nxtBlk) + blk_size(prevBlk));

        block = prevBlk;
    }

    return block;
}

/*
 * extend_heap - Extend heap with free block and return its block pointer
 */
static struct block *extend_heap(size_t words)
{
    void *bp = mem_sbrk(words * WSIZE);

    if (bp == NULL)
        return NULL;

    /* Initialize free block header/footer and the epilogue header.
     * Note that we overwrite the previous epilogue here. */
    struct block *blk = bp - sizeof(FENCE);

    // printf("extend_heap %p %i %i \n", blk, blk->header.inuse, blk->header.size);

    mark_block_free(blk, words);
    next_blk(blk)->header = FENCE;

    /* Coalesce if the previous block was free */
    return coalesce(blk);
}

/*
 * place - Place block of asize words at start of free block bp
 *         and split if remainder would be at least minimum block size
 */
static void place(void *bp, size_t asize)
{
    size_t csize = blk_size(bp);

    if ((csize - asize) >= MIN_BLOCK_SIZE_WORDS)
    {
        mark_block_used(bp, asize);
        bp = next_blk(bp);
        mark_block_free(bp, csize - asize);
    }
    else
    {
        mark_block_used(bp, csize);
    }
}

/*
 * find_fit - Find a fit for a block with asize words
 */
static struct block *find_fit(size_t asize)
{
    for (int i = getFreeListIndex(asize); i < 19; i++)
    {

        struct list *List = &FreeList[i];

        struct list_elem *end = list_end(List);

        for (struct list_elem *e = list_begin(List);
             e != end;
             e = e->next)
        {
            void *blk = list_entry(e, struct free_block, elem);

            if (asize <= blk_size(blk))
            {
                return blk;
            }
        }
    }

    return NULL; /* No fit */
}
