/*
 * mm.c
 *
 * Name: Shreel Shah
 *
 * Implementing dynamic memory allocation through the use of segregated free lists. Main functions being implemented are malloc, free and realloc, and to iterate the seg list, the creatoion of two new functions (insert and delete) are needed. 
 * This implementation is much more efficient than explicit because each size class will have its own free list.
 * Free lists will correspond to seg lists whose headers will be divided into classes based on 2^i sizes. 
 * To allocate a given block, the implementation searches for the appropriate sized list, and if a fit is found, then we split/place fragment on the list. 
 * If I do not find a block that corresponds, I simply look for the class that has a larger size that fits. Repeat this process, until a match is found. 
 * If no match is found within our classes, I place as a single free block in the largest defined class that we created based on the power of 2.
 * Next block and prev block are tracked through the use of the next free block pointer and prev free blk pointer, different from implicit where we stored sizes
 * Every block will have a header and a footer - header and footer contains size, allocated bit, 
 * In the explicit free list implementation that the seg list implementation builds on, for the allocated blocks we had a size, with the last bit being the allocated bit, payload, and the footer will the size and allocated bit.
 * The free blocks were structured: Header - Size and allocatation bit, Next pointer, Prev pointer. The footer had the size and the allocated bit.
 * Code referenced in the helper functions and the main 3 functions is referenced from the assigned class textbook: Computer Systems: A Programmer's Perspective (3rd Edition)
 * Also, read malloclab.pdf carefully and in its entirety before beginning.
 *
 */
#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <stdint.h>
#include <stdbool.h>

#include "mm.h"
#include "memlib.h"

/*
 * If you want to enable your debugging output and heap checker code,
 * uncomment the following line. Be sure not to have debugging enabled
 * in your final submission.
 */
 //#define DEBUG

#ifdef DEBUG
// When debugging is enabled, the underlying functions get called
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
#else
// When debugging is disabled, no code gets generated
#define dbg_printf(...)
#define dbg_assert(...)
#endif // DEBUG

// do not change the following!
#ifdef DRIVER
// create aliases for driver tests
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mm_memset
#define memcpy mm_memcpy
#endif // DRIVER

#define ALIGNMENT 16
//global
static size_t WSIZE = 8; //word and header/footer size - 16 bit aligned as per instructions
static size_t DSIZE = 16; //double word size
static size_t CHUNKSIZE = 1 << 5; //size to extend the heap - 32 for optimization
static char *heap_listp; //init empty heap
static char *free_list = 0; //start of free list (init empty)

static char * seg[11]; //seg list array with size class ptr's (11)

// rounds up to the nearest multiple of ALIGNMENT
static size_t align(size_t x)
{
    return ALIGNMENT * ((x+ALIGNMENT-1)/ALIGNMENT);
}
static size_t MAX(size_t x, size_t y) //Max and min func
{
    if (x > y){
        return x;
    }
    return y;
}
static size_t MIN(size_t x, size_t y)
{
    if (x < y)
    {
        return x;
    }
    return y;
}

static size_t PACK(size_t size, int alloc) //pack a size and allocated bit into word
{
    return (size | alloc);
}

static size_t GET(void* p) //read and write a word at address p
{
    return (*(size_t *) p);
}
static size_t PUT(void * p, size_t val)
{
    return (*((size_t *)p) = val);
}
static size_t GET_SIZE(void * p) //read the size and allocated fields from address p
{
    return (size_t)(GET(p) & ~(0xf));
}
static size_t GET_ALLOC(void * p)
{
    return (size_t)(GET(p) & 0x1);
}

static char * HDRP(void *bp) //using block pointer compute the address of header and footer
{ 
    return ((char *)(bp) - WSIZE);
}
static char* FTRP(void *bp)
{
    return ((char *) (bp) + GET_SIZE(HDRP(bp)) - DSIZE);
}
static char* NEXT_BLKP(void *bp) //computer address of next and prev blocks
{
    return ((char*)bp + GET_SIZE(((char *)(bp) - WSIZE)));
}
static char* PREV_BLKP(void *bp)
{
    return ((char*)bp - GET_SIZE(((char *)(bp) - DSIZE)));
}
static void* NEXTF(void*bp) //compute address of next and previous bp in the free list
{
    return (*(char**)(bp+WSIZE));
}
static void* PREVF(void*bp)
{
    return (*(char**)(bp));
}
//size classes based on powers of 2 - search for the appropriate sized list and return that index, we have 11 size classes
static int iterate(size_t size){ 
    if(size < 32){
        return 0;
    }
    else if ((size >= 32) && (size < 64))
    {
        return 1;
    }
    else if ((size >= 64) && (size < 128))
    {
        return 2;
    }
    else if ((size >= 128) && (size < 256))
    {
        return 3;
    }
    else if ((size >= 256) && (size < 512))
    {
        return 4;
    }
    else if ((size >= 512) && (size < 1024))
    {
        return 5;
    }
    else if ((size >= 1024) && (size < 2048))
    {
        return 6;
    }
    else if ((size >= 2048) && (size < 4096))
    {
        return 7;
    }
    else if ((size >= 4096) && (size < 8192))
    {
        return 8;
    }
    else if ((size >= 8192) && (size < 16384))
    {
        return 9;
    }
    return 10;
  
    
}


static void delete(void * bp)
{
   
   int i = 0;
   while(i != 11){ //iterate through  amount of size classes
       if (bp == seg[i]){
            if(PREVF(bp) == 0 && NEXTF(bp) != 0) //prev doesnt exist, next does
            {
                //free_list = NEXTF(bp); //set start of list to next free 
                 PUT(NEXTF(bp), 0); //set next blocks prev to 0
                 seg[i] = NEXTF(bp);
                 return;
            } 
            else  //only one free block in the list
            {
                //free_list = 0;
                seg[i] = 0;
                return;
            }
            
       }
     i += 1; //increment
   }

   if (PREVF(bp) != 0 && NEXTF(bp) == 0) //at end of list
   {
       PUT((PREVF(bp) + WSIZE), 0); // prev blocks next to 0
   }
   else{
       PUT(NEXTF(bp), (size_t)PREVF(bp)); //set prev blocks next to point to bp next
       PUT(PREVF(bp) + WSIZE, (size_t)NEXTF(bp));  //set nexts prev to prev
   }
   
    
}
static void insert(void * bp)
{
    size_t size = GET_SIZE(HDRP(bp)); //select the correct sized list
    int find = iterate(size); 
    if(seg[find]!= 0){ //list is not empty
        PUT(bp+WSIZE, (size_t)seg[find]); // bp next to head of list
        PUT(seg[find], (size_t)bp); //current head of the lists prev to bp
        PUT(bp,0); //set bp prev to 0
        //free_list = bp; //head to bp
        seg[find] = bp; //start of seg list
       
    }
    else
    {
        PUT(bp + WSIZE, 0);  //list empty
        PUT(bp, 0);  //set prev and next to 0
        //free_list = bp; //head to bp
        seg[find] = bp; //start of seg list
    }
    
    

}

static void *coalesce(void *bp) //figure 9.46 from Computer Systems Prog. Perspectives textbook - avoid fragmentation when not needed and adjust size of memory for more allocation space
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))) || PREV_BLKP(bp) == bp;
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if(prev_alloc && next_alloc){ //if both allocated, insert bp
        insert(bp);
        return bp;
    }
    else if (prev_alloc && !next_alloc) //prev allocated but not next
    {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); 
        delete(NEXT_BLKP(bp)); //delete the next block
        //insert(bp); 
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc) //prev not allocated but next is 
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        delete(PREV_BLKP(bp)); //delete prev
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        bp = PREV_BLKP(bp);
        
    }
    else
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))); //none allocated
        delete(PREV_BLKP(bp)); //delete prev
        delete(NEXT_BLKP(bp)); //delete next
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size,0));
        bp = PREV_BLKP(bp);
        
        
    }
    insert(bp); //insert
    return bp;
}

static void *extend_heap(size_t words) //fig 9.45 from Computer Systems Prog. Perspectives textbook - extends the heap with new free block
{
    char *bp;
    size_t size;
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE; //allocates even number of words for align maintenence 
    if ((long)(bp = mem_sbrk(size)) == -1)
    {
        return NULL;
    } 
    PUT(HDRP(bp), PACK(size, 0)); //initialize free block header/footer and epilogue header
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1));
    return coalesce(bp); //coalesce if the previous block was free
} 

/*
 * mm_init: returns false on error, true on success.
 */
bool mm_init(void) //9.44
{
    //mm_checkheap(__LINE__);
    int i;
    for (i = 0; i < 11; i++) //initialization of seg lists
    {
        seg[i] = 0;
    }
    // IMPLEMENT THIS
    if ((heap_listp = mem_sbrk(2*WSIZE)) == (void*)-1) //create the initial empty heap
    {
        return false;
    }
    PUT(heap_listp,0); //alignment padding
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE,1));//prologue header
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE,1)); //prologue footer
    PUT(heap_listp + (3*WSIZE), PACK(0,1)); //epilogue header
    heap_listp += (2*WSIZE);
    
    
    free_list = 0; //init free list to 0

    if(extend_heap(CHUNKSIZE) == NULL) //extend heapsize with free block of chunksize bytes
    {
        return false;
    } 
    return true;
    //mm_checkheap(__LINE__);
} 

static void *find_fit(size_t asize) //pg 920 of Computer Systems textbook - used to find the correct fit for the allocated amount 
{
    void *bp; //select seg list
    int find = iterate(asize); 
    for (int i = find; i < 11; i++) //traverse seg list
    {
        for (bp = seg[i]; bp != 0; bp = NEXTF(bp)) //iterate for a free block 
         {
            if(asize <= GET_SIZE(HDRP(bp)))
            {
            return bp;
            }
        }
    }
    
    return NULL; //fit not found
}
static void place(void *bp, size_t asize) //pg 920 of Computer Systems textbook - place block at beg of the block which is free and splits if the size of the remainder of the block is greater or equal to the min block size
{
    size_t csize = GET_SIZE(HDRP(bp));
    if ((csize - asize) >= (2*DSIZE)){
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        delete(bp);
        bp = NEXT_BLKP(bp); //new smaller block
        PUT(HDRP(bp), PACK(csize-asize, 0)); //put new smaller block header
        PUT(FTRP(bp), PACK(csize-asize, 0));  //new smaller block footer
        coalesce(bp); 
    }
    else{ //block not large enough to split
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
        delete(bp);
    }
}
/*
 * malloc
 */
void* malloc(size_t size) //9.47 from Computer Systems textbook - allocates a block from free list
{
    // IMPLEMENT THIS
    mm_checkheap(__LINE__);
    
    size_t asize; //adjusted block size
    size_t extendsize;  //amount to extend heap if no fit
    char* bp;

    if (size == 0) //ignorious spurious requests
    {
        return NULL;
    }
    if (size <= DSIZE) //adjust block size to include overhead and alignment reps
    {
        asize = 2*DSIZE;
    }
    else{
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
    }
    if ((bp = find_fit(asize)) != NULL) //search the free list for fit
    { 
        place(bp, asize);
        return bp;
    }
    extendsize = MAX(asize, CHUNKSIZE); //no fit found. get more memory and place the block
    if ((bp =extend_heap(extendsize/WSIZE)) == NULL){
        return NULL;
    }
    place(bp, asize);
    mm_checkheap(__LINE__);
    return bp;
}

/*
 * free
 */
void free(void* ptr)  //9.46 from Computer Systems textbook - frees a block and uses boudnary-tag coalescing to merge with adjacent free blocks
{
    // IMPLEMENT THIS
    
    size_t size = GET_SIZE(HDRP(ptr));
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size,0));
    coalesce(ptr);
   
   

}

/*
 * realloc
 */
void* realloc(void* oldptr, size_t size) //reassigning new set of memory
{
    // IMPLEMENT THIS
    mm_checkheap(__LINE__);
    void *update = malloc(size); //create a new pointer and allocate the size passed
    if (oldptr == NULL){
        return malloc(size); //if pointer is null the call is malloc(size)
    }
    if (size == 0) //if size is 0 the the call is free(ptr)
    {
        free(oldptr);
        return NULL;
    }
    size_t update_size = MIN(GET_SIZE(HDRP(oldptr)) - WSIZE, size); //could change size of the memory block 
    memcpy(update, oldptr, update_size); //realloc by calling memcopy function
    free(oldptr);
    mm_checkheap(__LINE__);
    return update;
}

/*
 * calloc
 * This function is not tested by mdriver, and has been implemented for you.
 */
void* calloc(size_t nmemb, size_t size)
{
    void* ptr;
    size *= nmemb;
    ptr = malloc(size);
    if (ptr) {
        memset(ptr, 0, size);
    }
    return ptr;
}

/*
 * Returns whether the pointer is in the heap.
 * May be useful for debugging.
 */
static bool in_heap(const void* p)
{
    return p <= mm_heap_hi() && p >= mm_heap_lo();
}

/*
 * Returns whether the pointer is aligned.
 * May be useful for debugging.
 */
static bool aligned(const void* p)
{
    size_t ip = (size_t) p;
    return align(ip) == ip;
}

/*
 * mm_checkheap
 */
bool mm_checkheap(int lineno)
{
#ifdef DEBUG
void * bp; 
printf("\nHeap Check: \n");
for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
{
    printf("Location: %p, size: %ld, a: %ld, \n", bp, GET_SIZE(HDRP(bp)), GET_ALLOC(HDRP(bp))); //heap checker - prints the location, size, and allocation bit of hdr
}
#endif // DEBUG
    return true;
}
