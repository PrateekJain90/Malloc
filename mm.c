/*
 * mm.c
 * 
 * Prateek Jain - prateekj
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
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
#define DEBUGx
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
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
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)


/*
 * If NEXT_FIT defined use next fit search, else use first fit search 
 */
#define NEXT_FITx

/* $begin mallocmacros */
/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */ //line:vm:mm:beginconst
#define DSIZE       8       /* Doubleword size (bytes) */
#define CHUNKSIZE  (1<<12)  /* Extend heap by this amount (bytes) */  //line:vm:mm:endconst 

#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc)) //line:vm:mm:pack

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))            //line:vm:mm:get
#define PUT(p, val)  (*(unsigned int *)(p) = (val))    //line:vm:mm:put

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)                   //line:vm:mm:getsize
#define GET_ALLOC(p) (GET(p) & 0x1)                    //line:vm:mm:getalloc

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)                      //line:vm:mm:hdrp
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) //line:vm:mm:ftrp

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) //line:vm:mm:nextblkp
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) //line:vm:mm:prevblkp


/* Given block ptr bp, find next and previous free blocks*/
// 4 to 8 byte conversion

//#define NEXT_PTR(bp)   (void *)(unsigned long)(*(unsigned int *)((char *)(bp) + WSIZE))
//#define PREV_PTR(bp)   (void *)(unsigned long)(*(unsigned int *)((char *)(bp)))

#define NEXT_PTR(bp)   ((char *)(bp) + WSIZE)
#define PREV_PTR(bp)   ((char *)(bp))

/* Global variables */
static char *heap_listp = 0;  /* Pointer to first block */  
static char *freeListHeader = NULL;

#ifdef NEXT_FIT
static char *rover;           /* Next fit rover */
#endif
/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void printblock(void *bp); 
static void checkheap(int verbose);
static void checkblock(void *bp);
static void addToFreeList(void *bp);
static void deleteFromFreeList(void *bp);

/* Given a an offset, convert it to actual address */
static inline void *actualAddressFromOffset(int offset)
{
	dbg_printf("Offset is : %d\n",offset);

	if(offset==0)
		return NULL;

	return (void *)(offset + heap_listp);
}

/* Given an address, convert it to an offset */
static inline int offsetFromActualAddress(void *bp)
{
	dbg_printf("Offset from actual address called..\n");
	
	if(!bp)
		return 0;

	return (int)((char*)bp - heap_listp);
}


/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) {

	heap_listp = 0;  /* Pointer to first block */  
	freeListHeader = NULL;
	
	/* Create the initial empty heap */
	if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1) //line:vm:mm:begininit
		return -1;
	PUT(heap_listp, 0);                          /* Alignment padding */
	PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */ 
	PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */ 
	PUT(heap_listp + (3*WSIZE), PACK(0, 1));     /* Epilogue header */
	heap_listp += (2*WSIZE);                     //line:vm:mm:endinit  
	/* $end mminit */

#ifdef NEXT_FIT
	rover = heap_listp;
#endif
	/* $begin mminit */

	/* Extend the empty heap with a free block of CHUNKSIZE bytes */
	if (extend_heap(CHUNKSIZE/WSIZE) == NULL) 
		return -1;

	return 0;
}
/* $end mminit */


/*
 * malloc
 */
void *malloc (size_t size) {
	size_t asize;      /* Adjusted block size */
	size_t extendsize; /* Amount to extend heap if no fit */
	char *bp;      

	/* $end mmmalloc */
	if (heap_listp == 0){
		mm_init();
	}
	/* $begin mmmalloc */
	/* Ignore spurious requests */
	if (size == 0)
		return NULL;

	/* Adjust block size to include overhead and alignment reqs. */
	if (size <= DSIZE)                                          //line:vm:mm:sizeadjust1
		asize = 2*DSIZE;                                        //line:vm:mm:sizeadjust2
	else
		asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE); //line:vm:mm:sizeadjust3

	/* Search the free list for a fit */
	if ((bp = find_fit(asize)) != NULL) {  //line:vm:mm:findfitcall
		place(bp, asize);                  //line:vm:mm:findfitplace
		return bp;
	}

	/* No fit found. Get more memory and place the block */
	extendsize = MAX(asize,CHUNKSIZE);                 //line:vm:mm:growheap1
	if ((bp = extend_heap(extendsize/WSIZE)) == NULL)  
		return NULL;                                  //line:vm:mm:growheap2
	place(bp, asize);                                 //line:vm:mm:growheap3
	return bp;
}

/*
 * free
 */
void free (void *bp) {
	/* $end mmfree */
	if(bp == 0) 
		return;

	/* $begin mmfree */
	size_t size = GET_SIZE(HDRP(bp));
	/* $end mmfree */
	if (heap_listp == 0){
		mm_init();
	}
	/* $begin mmfree */

	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));
	coalesce(bp);
}

/*
 * realloc - you may want to look at mm-naive.c
 */
void *realloc(void *oldptr, size_t size) {

	size_t oldsize;
	void *newptr;

	/* If size == 0 then this is just free, and we return NULL. */
	if(size == 0) {
		mm_free(oldptr);
		return 0;
	}

	/* If oldptr is NULL, then this is just malloc. */
	if(oldptr == NULL) {
		return mm_malloc(size);
	}

	newptr = mm_malloc(size);

	/* If realloc() fails the original block is left untouched  */
	if(!newptr) {
		return 0;
	}

	/* Copy the old data. */
	oldsize = GET_SIZE(HDRP(oldptr));
	if(size < oldsize) oldsize = size;
	memcpy(newptr, oldptr, oldsize);

	/* Free the old block. */
	mm_free(oldptr);

	return newptr;

}

/*
 * calloc - you may want to look at mm-naive.c
 * This function is not tested by mdriver, but it is
 * needed to run the traces.
 */
void *calloc (size_t nmemb, size_t size) {
	size_t bytes = nmemb * size;
	void *newptr;

	newptr = malloc(bytes);
	memset(newptr, 0, bytes);

	return newptr;
}


/*
 * Return whether the pointer is in the heap.
 * May be useful for debugging.
 */
static int in_heap(const void *p) {
	return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Return whether the pointer is aligned.
 * May be useful for debugging.
 */
static int aligned(const void *p) {
	return (size_t)ALIGN(p) == (size_t)p;
}

/*
 * mm_checkheap
 */
void mm_checkheap(int lineno) {
	if(lineno)
		checkheap(lineno);
}

/* 
 * The remaining routines are internal helper routines 
 */

/*
 * coalesce - Boundary tag coalescing. Return ptr to coalesced block
 */
static void *coalesce(void *bp) 
{
	size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
	size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	size_t size = GET_SIZE(HDRP(bp));

	if (prev_alloc && next_alloc) {            /* Case 1 */
		addToFreeList(bp);
		return bp;
	}

	else if (prev_alloc && !next_alloc) {      /* Case 2 */
	
		deleteFromFreeList(NEXT_BLKP(bp));	

		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size,0));
	}

	else if (!prev_alloc && next_alloc) {      /* Case 3 */
		
		deleteFromFreeList(PREV_BLKP(bp));	
		
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		PUT(FTRP(bp), PACK(size, 0));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
	}

	else {                                     /* Case 4 */
		
		deleteFromFreeList(NEXT_BLKP(bp));	
		deleteFromFreeList(PREV_BLKP(bp));	
		
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
			GET_SIZE(FTRP(NEXT_BLKP(bp)));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
	}
	
	addToFreeList(bp);
	
#ifdef NEXT_FIT
	/* Make sure the rover isn't pointing into the free block */
	/* that we just coalesced */
	if ((rover > (char *)bp) && (rover < NEXT_BLKP(bp))) 
		rover = bp;
#endif
	return bp;
}

/* 
 * extend_heap - Extend heap with free block and return its block pointer
 */
/* $begin mmextendheap */
static void *extend_heap(size_t words) 
{
	char *bp;
	size_t size;

	/* Allocate an even number of words to maintain alignment */
	size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; //line:vm:mm:beginextend
	if ((long)(bp = mem_sbrk(size)) == -1)  
		return NULL;                                        //line:vm:mm:endextend

	/* Initialize free block header/footer and the epilogue header */
	PUT(HDRP(bp), PACK(size, 0));         /* Free block header */   //line:vm:mm:freeblockhdr
	PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */   //line:vm:mm:freeblockftr
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */ //line:vm:mm:newepihdr

	/* Coalesce if the previous block was free */
	return coalesce(bp);                                          //line:vm:mm:returnblock
}
/* $end mmextendheap */

/* 
 * place - Place block of asize bytes at start of free block bp 
 *         and split if remainder would be at least minimum block size
 */
/* $begin mmplace */
/* $begin mmplace-proto */
static void place(void *bp, size_t asize)
	/* $end mmplace-proto */
{
	size_t csize = GET_SIZE(HDRP(bp));   
	deleteFromFreeList(bp);
	
	if ((csize - asize) >= (2*DSIZE)) { 
		PUT(HDRP(bp), PACK(asize, 1));
		PUT(FTRP(bp), PACK(asize, 1));

		bp = NEXT_BLKP(bp);
		PUT(HDRP(bp), PACK(csize-asize, 0));
		PUT(FTRP(bp), PACK(csize-asize, 0));
		addToFreeList(bp);
	}
	else { 
		PUT(HDRP(bp), PACK(csize, 1));
		PUT(FTRP(bp), PACK(csize, 1));
	}
}
/* $end mmplace */


/* 
 * find_fit - Find a fit for a block with asize bytes 
 */
/* $begin mmfirstfit */
/* $begin mmfirstfit-proto */
static void *find_fit(size_t asize)
	/* $end mmfirstfit-proto */
{
	/* $end mmfirstfit */

#ifdef NEXT_FIT 
	/* Next fit search */
	char *oldrover = rover;

	/* Search from the rover to the end of list */
	for ( ; GET_SIZE(HDRP(rover)) > 0; rover = NEXT_BLKP(rover))
		if (!GET_ALLOC(HDRP(rover)) && (asize <= GET_SIZE(HDRP(rover))))
			return rover;

	/* search from start of list to old rover */
	for (rover = heap_listp; rover < oldrover; rover = NEXT_BLKP(rover))
		if (!GET_ALLOC(HDRP(rover)) && (asize <= GET_SIZE(HDRP(rover))))
			return rover;

	return NULL;  /* no fit found */
#else 
	/* $begin mmfirstfit */
	/* First fit search */
	void *bp;
	
	dbg_printf("find fit called\n");
	for (bp = freeListHeader; bp && GET_SIZE(HDRP(bp)) > 0; bp = actualAddressFromOffset(GET(NEXT_PTR(bp)))) {
		
		dbg_printf("Inside Loop: bp header value is : %lx\n",(unsigned long)((unsigned long*)bp));
		if (asize <= GET_SIZE(HDRP(bp)) && !GET_ALLOC(HDRP(bp))) {
			dbg_printf("Requested: %zu, Gave: %d\n",asize,GET_SIZE(HDRP(bp)));
			return bp;
		}
	}
	return NULL; /* No fit */
	/* $end mmfirstfit */
#endif
}

static void printblock(void *bp) 
{
	size_t hsize, halloc, fsize, falloc;

	checkheap(0);
	hsize = GET_SIZE(HDRP(bp));
	halloc = GET_ALLOC(HDRP(bp));  
	fsize = GET_SIZE(FTRP(bp));
	falloc = GET_ALLOC(FTRP(bp));  

	if (hsize == 0) {
		printf("%p: EOL\n", bp);
		return;
	}

	/*  printf("%p: header: [%p:%c] footer: [%p:%c]\n", bp, 
		hsize, (halloc ? 'a' : 'f'), 
		fsize, (falloc ? 'a' : 'f')); */
}


static void checkblock(void *bp) 
{
	if (!aligned(bp))
		printf("Error: %p is not doubleword aligned\n", bp);
	if (GET(HDRP(bp)) != GET(FTRP(bp)))
		printf("Error: header does not match footer\n");
	if(!in_heap(bp))
		printf("Error: Block not within heap boundaries");
/*
	if(GET_ALLOC(HDRP(bp))==0)
	{
		void* prevFreeBlock = actualAddressFromOffset(GET(PREV_PTR(bp)));
		void* nextFreeBlock = actualAddressFromOffset(GET(NEXT_PTR(bp)));

		// Check consistency of next and previous pointers
		if(prevFreeBlock)
			if(!(actualAddressFromOffset(GET(NEXT_PTR(prevFreeBlock))) == bp))
				printf("Error: Previous free block does not point to current block");
		if(nextFreeBlock)
			if(!(actualAddressFromOffset(GET(PREV_PTR(nextFreeBlock))) == bp))
				printf("Error: Next free block does not point back to current block");

		// Check if previous and next pointers point between the 
		// beginning and end of heap 
		if(!in_heap(prevFreeBlock))
			printf("Error: Previous Free block not within heap boundaries");
		if(!in_heap(nextFreeBlock))
			printf("Error: Next Free block not within heap boundaries");
	}
*/
}

/* 
 * checkheap - Minimal check of the heap for consistency 
 */
void checkheap(int verbose) 
{
	char *bp = heap_listp;

	if (verbose)
		printf("Heap (%p):\n", heap_listp);

	if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp)))
		printf("Bad prologue header\n");
	checkblock(heap_listp);

	for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
		if (verbose) 
			printblock(bp);
		checkblock(bp);
	}

	if (verbose)
		printblock(bp);
	if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
		printf("Bad epilogue header\n");
}

static void deleteFromFreeList(void *bp)
{
	if(!bp)
	{
		dbg_printf("NULL received in deleteFromFreeList");
		return;
	}

	dbg_printf("Delete called....\n");
	
	//CASE 1 : Delete from the beginning of free list
	if(bp == freeListHeader)
	{
		int offsetValue = GET(NEXT_PTR(bp));
		
		if(0==offsetValue)
		{
			freeListHeader = NULL;
			PUT(NEXT_PTR(bp),0);
			PUT(PREV_PTR(bp),0);
		}	

		else if(offsetValue)
		{
			void *bp_nextBlock = actualAddressFromOffset(offsetValue);
			freeListHeader = bp_nextBlock;
			PUT(PREV_PTR(bp_nextBlock),0);
			PUT(NEXT_PTR(bp),0);
		}
	}

	// CASE 2 : Delete from the end of the free list
	else if(0 == GET(NEXT_PTR(bp)))
	{
		int offsetValue = GET(PREV_PTR(bp));

		if(offsetValue)
		{
			void *bp_prevBlock = actualAddressFromOffset(offsetValue);
			PUT(NEXT_PTR(bp_prevBlock),0);
		}

		PUT(PREV_PTR(bp),0);
	}

	// CASE 3 : Delete from middle of the free list
	else
	{	
		if((GET(PREV_PTR(bp))!=0) && (GET(NEXT_PTR(bp))!=0))
		{
			void *bp_prevBlock = actualAddressFromOffset(GET(PREV_PTR(bp)));
			void *bp_nextBlock = actualAddressFromOffset(GET(NEXT_PTR(bp)));
			
			PUT(NEXT_PTR(bp_prevBlock), GET(NEXT_PTR(bp)));
			PUT(PREV_PTR(bp_nextBlock), GET(PREV_PTR(bp)));
			PUT(NEXT_PTR(bp),0);
			PUT(PREV_PTR(bp),0);
		}

	}

	dbg_printf("Delete exited...\n");
}

static void addToFreeList(void *bp)
{
	if(!bp)
	{
		dbg_printf("NULL received in addToFreeList");
		return;
	}	

	dbg_printf("add called..\n");

	// If there is no block in free list
	if(!freeListHeader)
	{
		freeListHeader = bp;
		PUT(PREV_PTR(bp),0);
		PUT(NEXT_PTR(bp),0);
	}

	// Put block in the beginning of the free list
	else
	{
		PUT(NEXT_PTR(bp),offsetFromActualAddress(freeListHeader));
		PUT(PREV_PTR(bp),0);
		PUT(PREV_PTR(freeListHeader),offsetFromActualAddress(bp));
		freeListHeader = bp;
	}
	
	dbg_printf("add exited...\n");
}
