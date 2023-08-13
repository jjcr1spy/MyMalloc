#include <errno.h>
#include <pthread.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include "myMalloc.h"
#include "printing.h"

/* Due to the way assert() prints error messges we use out own assert function
 * for deteminism when testing assertions
 */
#ifdef TEST_ASSERT
  inline static void assert(int e) {
    if (!e) {
      const char * msg = "Assertion Failed!\n";
      write(2, msg, strlen(msg));
      exit(1);
    }
  }
#else
  #include <assert.h>
#endif

/*
 * Mutex to ensure thread safety for the freelist
 */
static pthread_mutex_t mutex;

/*
 * Array of sentinel nodes for the freelists
 */
header freelistSentinels[N_LISTS];

/*
 * Pointer to the second fencepost in the most recently allocated chunk from
 * the OS. Used for coalescing chunks
 */
header * lastFencePost;

/*
 * Pointer to maintian the base of the heap to allow printing based on the
 * distance from the base of the heap
 */ 
void * base;

/*
 * List of chunks allocated by the OS for printing boundary tags
 */
header * osChunkList [MAX_OS_CHUNKS];
size_t numOsChunks = 0;

/*
 * direct the compiler to run the init function before running main
 * this allows initialization of required globals
 */
static void init (void) __attribute__ ((constructor));

// Helper functions for manipulating pointers to headers
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off);
static inline header * get_left_header(header * h);
static inline header * ptr_to_header(void * p);


// Helper functions for allocating more memory from the OS
static inline void initialize_fencepost(header * fp, size_t left_size);
static inline void insert_os_chunk(header * hdr);
static inline void insert_fenceposts(void * raw_mem, size_t size);
static header * allocate_chunk(size_t size);

// Helper functions for freeing a block
static inline void deallocate_object(void * p);

// Helper functions for allocating a block
static inline header * allocate_object(size_t raw_size);

// Helper functions for verifying that the data structures are structurally 
// valid
static inline header * detect_cycles();
static inline header * verify_pointers();
static inline bool verify_freelist();
static inline header * verify_chunk(header * chunk);
static inline bool verify_tags();

static void init();

static bool isMallocInitialized;

/**
 * @brief Helper function to retrieve a header pointer from a pointer and an 
 *        offset
 *
 * @param ptr base pointer
 * @param off number of bytes from base pointer where header is located
 *
 * @return a pointer to a header offset bytes from pointer
 */
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off) {
	return (header *)((char *) ptr + off);
}

/**
 * @brief Helper function to get the header to the right of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
header * get_right_header(header * h) {
	return get_header_from_offset(h, get_size(h));
}

/**
 * @brief Helper function to get the header to the left of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
inline static header * get_left_header(header * h) {
  return get_header_from_offset(h, -h->left_size);
}

/**
 * @brief Fenceposts are marked as always allocated and may need to have
 * a left object size to ensure coalescing happens properly
 *
: * @param fp a pointer to the header being used as a fencepost
 * @param left_size the size of the object to the left of the fencepost
 */
inline static void initialize_fencepost(header * fp, size_t left_size) {
  set_state(fp,FENCEPOST);
  set_size(fp, ALLOC_HEADER_SIZE);
  fp->left_size = left_size;
}

/**
 * @brief Helper function to maintain list of chunks from the OS for debugging
 *
 * @param hdr the first fencepost in the chunk allocated by the OS
 */
inline static void insert_os_chunk(header * hdr) {
  if (numOsChunks < MAX_OS_CHUNKS) {
    osChunkList[numOsChunks++] = hdr;
  }
}

/**
 * @brief given a chunk of memory insert fenceposts at the left and 
 * right boundaries of the block to prevent coalescing outside of the
 * block
 *
 * @param raw_mem a void pointer to the memory chunk to initialize
 * @param size the size of the allocated chunk
 */
inline static void insert_fenceposts(void * raw_mem, size_t size) {
  // Convert to char * before performing operations
  char * mem = (char *) raw_mem;

  // Insert a fencepost at the left edge of the block
  header * leftFencePost = (header *) mem;
  initialize_fencepost(leftFencePost, ALLOC_HEADER_SIZE);

  // Insert a fencepost at the right edge of the block
  header * rightFencePost = get_header_from_offset(mem, size - ALLOC_HEADER_SIZE);
  initialize_fencepost(rightFencePost, size - 2 * ALLOC_HEADER_SIZE);
}

/**
 * @brief Allocate another chunk from the OS and prepare to insert it
 * into the free list
 *
 * @param size The size to allocate from the OS
 *
 * @return A pointer to the allocable block in the chunk (just after the 
 * first fencpost)
 */
static header * allocate_chunk(size_t size) {
  void * mem = sbrk(size);
  
  insert_fenceposts(mem, size);
  header * hdr = (header *) ((char *)mem + ALLOC_HEADER_SIZE);
  set_state(hdr, UNALLOCATED);
  set_size(hdr, size - 2 * ALLOC_HEADER_SIZE);
  hdr->left_size = ALLOC_HEADER_SIZE;
  return hdr;
}

static inline int get_index(int size) {
  return (size / 8 - 4 < N_LISTS - 1) ? (size / 8 - 4) : N_LISTS - 1;
}

static void insert_new_chunk() {
  header * chunk = allocate_chunk(ARENA_SIZE); // allocate new chunk
  header * prevChunkFence = (header *) ((char *) chunk - 2 * ALLOC_HEADER_SIZE);
	  
  if (get_state(prevChunkFence) == FENCEPOST) { // merge the neighboring chunks
    header * obj = get_left_header(prevChunkFence);
    if (get_state(obj) == UNALLOCATED) { // merge which new chunk
      int i = get_size(obj) / 8 - 4 <= N_LISTS - 1 ? get_size(obj) / 8 - 4 : N_LISTS - 1; 
      if (i != N_LISTS - 1) {
        obj->next->prev = obj->prev; // remove from freelist
	obj->prev->next = obj->next;

	header * sent = &freelistSentinels[N_LISTS - 1];

	obj->next = sent->next;
	obj->prev = sent; 

	sent->next = obj;
	obj->next->prev = obj;
      }
      obj->size_state += ARENA_SIZE;
      header * h = get_right_header(obj);
      h->left_size = get_size(obj);
    } else { // block is allocated, so just edit prev chunks last fencepost
      prevChunkFence->size_state += (ARENA_SIZE - ALLOC_HEADER_SIZE);
      set_state(prevChunkFence, UNALLOCATED);
   
      header * sent = &freelistSentinels[N_LISTS - 1];

      prevChunkFence->next = sent->next;
      prevChunkFence->prev = sent; 

      sent->next = prevChunkFence;
      prevChunkFence->next->prev = prevChunkFence;

      header * h = get_right_header(prevChunkFence);
      h->left_size = get_size(prevChunkFence);
    }
  } else { // not neighbors 
    insert_os_chunk((header *) ((char *) chunk - ALLOC_HEADER_SIZE));
    header * sent = &freelistSentinels[N_LISTS - 1];

    chunk->next = sent->next;
    chunk->prev = sent;

    sent->next = chunk;
    chunk->next->prev = chunk;
  }
}

static header * find_block(int index, size_t total) {
  while (1) {
    if (index == N_LISTS - 1) { // when in last index, also make sure size of block >= total
      header * sent = &freelistSentinels[index];
      header * iter = sent->next;
      while (iter != sent) {
        if (get_size(iter) >= total) {
	  return iter; // block found
        }
        iter = iter->next;
      }
    } else { // just check if list is simply empty or not when finding block
      for (int i = index; i < N_LISTS; i++) {		
        header * temp = &freelistSentinels[i];
        if (temp->next != temp) {
          return temp->next;
        }
      }
    }
    insert_new_chunk();// if we get here, block not found so allocate more memory and search again!
  }
}

/**
 * @brief Helper allocate an object given a raw request size from the user
 *
 * @param raw_size number of bytes the user needs
 *
 * @return A block satisfying the user's request
 */
static inline header * allocate_object(size_t raw_size) {
  size_t total;
  
  if (raw_size == 0) return NULL;
  else total = raw_size;

  total = (total + 7) & ~0x7; // round to multiple of 8 
  total = total + ALLOC_HEADER_SIZE < sizeof(header) ? sizeof(header) : total + ALLOC_HEADER_SIZE; // min malloc size is sizeof(header)

  int index = get_index(total); // we subtract 4 not 2 since total includes ALLOC_HEADER_SIZE
								      
  header * target = find_block(index, total);  
  
  target->prev->next = target->next; // remove target from freelist 
  target->next->prev = target->prev; 
    
  int remainder = get_size(target) - total;
  set_size_and_state(target, total, ALLOCATED); // update target state/size

  if (remainder >= sizeof(header)) { // split the block and add another header 
    header * new_head = get_header_from_offset(target, total); // create new header
    set_size_and_state(new_head, remainder, UNALLOCATED);
    new_head->left_size = total; 
    
    int index = get_index(remainder);
    header * sent = &freelistSentinels[index];

    new_head->prev = sent; // update prev/next since block is unallocated
    new_head->next = sent->next;

    sent->next = new_head; // update freelist links
    new_head->next->prev = new_head;
	
    header * right = get_right_header(new_head); // update right headers->left_size
    right->left_size = remainder;
  } else if (remainder != 0) { // need to add additional bytes for header alignment
    target->size_state += remainder;
  }
  
  return (header *) ((char *) target + ALLOC_HEADER_SIZE);
}

/**
 * @brief Helper to get the header from a pointer allocated with malloc
 *
 * @param p pointer to the data region of the block
 *
 * @return A pointer to the header of the block
 */
static inline header * ptr_to_header(void * p) {
  return (header *)((char *) p - ALLOC_HEADER_SIZE); //sizeof(header));
}

static void left_unalloc(header * obj, header * left) {
  int index = get_index(get_size(left));
  if (index != N_LISTS - 1) { // make sure not last index of freelist	
    left->prev->next = left->next; // remove from freelist
    left->next->prev = left->prev; 

    header * sent = &freelistSentinels[get_index(get_size(obj) + get_size(left))]; // get freelist sentinel
    left->prev = sent; // update links
    left->next = sent->next;
    
    sent->next = left; // add to freelist
    left->next->prev = left;
  }
  left->size_state += get_size(obj); // update size and state of header we keep
  set_state(left, UNALLOCATED); 

  header * r = get_right_header(left); // update right headers->left_size
  r->left_size = get_size(left);
}

static void right_unalloc(header * obj, header * right) {
  obj->size_state += get_size(right); // update size and state of header we keep
  set_state(obj, UNALLOCATED);

  int index = get_index(get_size(right));
  if (index != N_LISTS - 1) { // make sure not last index of freelist
    right->prev->next = right->next; // remove from freelist
    right->next->prev = right->prev;    

    header * sent = &freelistSentinels[get_index(get_size(obj))]; // get freelist sentinel

    obj->prev = sent; // update links
    obj->next = sent->next;
	 
    sent->next = obj; // add to freelist
    obj->next->prev = obj;
  } else {
    obj->prev = right->prev; // update pre/next pointers
    obj->next = right->next;

    obj->next->prev = obj; // make sure obj's neighbors point to obj not right
    obj->prev->next = obj;
  }
  header * r = get_right_header(right); // update right headers->left_size
  r->left_size = get_size(obj);
}

static void both_unalloc(header * obj, header * left, header * right) {
  int right_index = get_index(get_size(right));
  int left_index = get_index(get_size(left));

  left->size_state += get_size(obj) + get_size(right); // updates new headers state and size
  set_state(left, UNALLOCATED);

  if (left_index == N_LISTS - 1) { // use left's freelist pointers 
    right->prev->next = right->next; // remove from freelist
    right->next->prev = right->prev;    
  } else if (right_index == N_LISTS - 1) { // use right's freelist pointers
    left->prev->next = left->next; // remove from freelist
    left->next->prev = left->prev;
   
    left->prev = right->prev; // use rights pointers
    left->next = right->next; 

    left->prev->next = left; // point to proper header
    left->next->prev = left;
  } else { // just remove both left/right pointers and insert new one
    left->prev->next = left->next; // remove from freelist
    left->next->prev = left->prev;

    right->prev->next = right->next; // remove from freelist
    right->next->prev = right->prev; 

    header * sent = &freelistSentinels[get_index(get_size(left))]; // get freelist sentinel

    left->prev = sent; // update links
    left->next = sent->next;
	 
    sent->next = left; // add to freelist
    left->next->prev = left;
  }
  header * r = get_right_header(left); // update right headers->left_size
  r->left_size = get_size(left);
}

static void both_alloc(header * obj) {
  set_state(obj, UNALLOCATED); // update state 
		
  int index = get_index(get_size(obj));
  header * sent = &freelistSentinels[index]; // get freelist sentinel

  obj->prev = sent; // update prev/next
  obj->next = sent->next;
	
  sent->next = obj; // add to freelist
  obj->next->prev = obj;
}

/**
 * @brief Helper to manage deallocation of a pointer returned by the user
 *
 * @param p The pointer returned to the user by a call to malloc
 */
static inline void deallocate_object(void * p) {
  if (p == NULL) return;

  header * obj = ptr_to_header(p);
  header * left = get_left_header(obj);
  header * right = get_right_header(obj);

  if (get_state(obj) == 0) {
    printf("Double Free Detected\n");
    assert(0);
  }
   
  if (get_state(left) == 0 && get_state(right) > 0) { // case 1. left unalloc
    left_unalloc(obj, left);
  } else if (get_state(right) == 0 && get_state(left) > 0) { // case 2, right unalloc
    right_unalloc(obj, right);
  } else if (get_state(left) > 0 && get_state(right) > 0) { // case 3, both alloc
    both_alloc(obj);
  } else { // case 4, both unalloc
    both_unalloc(obj, left, right);
  }
}

/**
 * @brief Helper to detect cycles in the free list
 * https://en.wikipedia.org/wiki/Cycle_detection#Floyd's_Tortoise_and_Hare
 *
 * @return One of the nodes in the cycle or NULL if no cycle is present
 */
static inline header * detect_cycles() {
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    for (header * slow = freelist->next, * fast = freelist->next->next; fast != freelist; slow = slow->next, fast = fast->next->next) {
      if (slow == fast) {
        return slow;
      }
    }
  }
  return NULL;
}

/**
 * @brief Helper to verify that there are no unlinked previous or next pointers
 *        in the free list
 *
 * @return A node whose previous and next pointers are incorrect or NULL if no
 *         such node exists
 */
static inline header * verify_pointers() {
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    for (header * cur = freelist->next; cur != freelist; cur = cur->next) {
      if (cur->next->prev != cur || cur->prev->next != cur) {
        return cur;
      }
    }
  }
  return NULL;
}

/**
 * @brief Verify the structure of the free list is correct by checkin for 
 *        cycles and misdirected pointers
 *
 * @return true if the list is valid
 */
static inline bool verify_freelist() {
  header * cycle = detect_cycles();
  if (cycle != NULL) {
    fprintf(stderr, "Cycle Detected\n");
    print_sublist(print_object, cycle->next, cycle);
    return false;
  }

  header * invalid = verify_pointers();
  if (invalid != NULL) {
    fprintf(stderr, "Invalid pointers\n");
    print_object(invalid);
    return false;
  }

  return true;
}

/**
 * @brief Helper to verify that the sizes in a chunk from the OS are correct
 *        and that allocated node's canary values are correct
 *
 * @param chunk AREA_SIZE chunk allocated from the OS
 *
 * @return a pointer to an invalid header or NULL if all header's are valid
 */
static inline header * verify_chunk(header * chunk) {
	if (get_state(chunk) != FENCEPOST) {
		fprintf(stderr, "Invalid fencepost\n");
		print_object(chunk);
		return chunk;
	}
	
	for (; get_state(chunk) != FENCEPOST; chunk = get_right_header(chunk)) {
		if (get_size(chunk)  != get_right_header(chunk)->left_size) {
			fprintf(stderr, "Invalid sizes\n");
			print_object(chunk);
			return chunk;
		}
	}
	
	return NULL;
}

/**
 * @brief For each chunk allocated by the OS verify that the boundary tags
 *        are consistent
 *
 * @return true if the boundary tags are valid
 */
static inline bool verify_tags() {
  for (size_t i = 0; i < numOsChunks; i++) {
    header * invalid = verify_chunk(osChunkList[i]);
    if (invalid != NULL) {
      return invalid;
    }
  }

  return NULL;
}

/**
 * @brief Initialize mutex lock and prepare an initial chunk of memory for allocation
 */
static void init() {
  // Initialize mutex for thread safety
  pthread_mutex_init(&mutex, NULL);

#ifdef DEBUG
  // Manually set printf buffer so it won't call malloc when debugging the allocator
  setvbuf(stdout, NULL, _IONBF, 0);
#endif // DEBUG

  // Allocate the first chunk from the OS
  header * block = allocate_chunk(ARENA_SIZE);

  header * prevFencePost = get_header_from_offset(block, -ALLOC_HEADER_SIZE);
  insert_os_chunk(prevFencePost);
  lastFencePost = get_header_from_offset(block, get_size(block));

  // Set the base pointer to the beginning of the first fencepost in the first
  // chunk from the OS
  base = ((char *) block) - ALLOC_HEADER_SIZE; //sizeof(header);

  // Initialize freelist sentinels
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    freelist->next = freelist;
    freelist->prev = freelist;
  }

  // Insert first chunk into the free list
  header * freelist = &freelistSentinels[N_LISTS - 1];
  freelist->next = block;
  freelist->prev = block;
  block->next = freelist;
  block->prev = freelist;
}

/* 
 * External interface
 */
void * my_malloc(size_t size) {
  pthread_mutex_lock(&mutex);
  header * hdr = allocate_object(size); 
  pthread_mutex_unlock(&mutex);
  return hdr;
}

void * my_calloc(size_t nmemb, size_t size) {
  return memset(my_malloc(size * nmemb), 0, size * nmemb);
}

void * my_realloc(void * ptr, size_t size) {
  void * mem = my_malloc(size);
  memcpy(mem, ptr, size);
  my_free(ptr);
  return mem; 
}

void my_free(void * p) {
  pthread_mutex_lock(&mutex);
  deallocate_object(p);
  pthread_mutex_unlock(&mutex);
}

bool verify() {
  return verify_freelist() && verify_tags();
}
