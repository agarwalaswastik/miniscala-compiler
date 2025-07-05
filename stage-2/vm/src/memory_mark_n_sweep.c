#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

#include "memory.h"
#include "fail.h"
#include "engine.h"

#if GC_VERSION == GC_MARK_N_SWEEP

static void* memory_start = NULL;
static void* memory_end = NULL;

static uvalue_t* bitmap_start = NULL;

static value_t* heap_start = NULL;
static value_t* heap_end = NULL;
static value_t heap_start_v = 0;
static value_t heap_end_v = 0;
static value_t* heap_first_block = NULL;

#define FREE_LISTS_COUNT 32
static value_t* free_list_heads[FREE_LISTS_COUNT];

#define MIN_BLOCK_SIZE 1
#define HEADER_SIZE 1

// Header management

static value_t header_pack(tag_t tag, value_t size) {
  return (size << 8) | (value_t)tag;
}

static tag_t header_unpack_tag(value_t header) {
  return (tag_t)(header & 0xFF);
}

static value_t header_unpack_size(value_t header) {
  return header >> 8;
}

#define get_block_size(b) header_unpack_size((b)[-1])
#define get_block_tag(b) header_unpack_tag((b)[-1])

// Bitmap management

static int bitmap_is_bit_set(value_t* ptr) {
  assert(heap_start <= ptr && ptr < heap_end);
  long index = ptr - heap_start;
  long word_index = index / (long)VALUE_BITS;
  long bit_index = index % (long)VALUE_BITS;
  return (bitmap_start[word_index] & ((uvalue_t)1 << bit_index)) != 0;
}

static void bitmap_set_bit(value_t* ptr) {
  assert(heap_start <= ptr && ptr < heap_end);
  long index = ptr - heap_start;
  long word_index = index / (long)VALUE_BITS;
  long bit_index = index % (long)VALUE_BITS;
  bitmap_start[word_index] |= (uvalue_t)1 << bit_index;
}

static void bitmap_clear_bit(value_t* ptr) {
  assert(heap_start <= ptr && ptr < heap_end);
  long index = ptr - heap_start;
  long word_index = index / (long)VALUE_BITS;
  long bit_index = index % (long)VALUE_BITS;
  bitmap_start[word_index] &= ~((uvalue_t)1 << bit_index);
}

// Virtual <-> physical address translation

static void* addr_v_to_p(value_t v_addr) {
  return (char*)memory_start + v_addr;
}

static value_t addr_p_to_v(void* p_addr) {
  return (value_t)((char*)p_addr - (char*)memory_start);
}

// Helpers

int in_blocks(value_t* p) {
  return heap_first_block <= p && p < heap_end;
}

int in_blocks_v(value_t v) {
  return in_blocks(addr_v_to_p(v));
}

// Free lists management

static value_t real_size(value_t size) {
  assert(0 <= size);
  return size < MIN_BLOCK_SIZE ? MIN_BLOCK_SIZE : size;
}

static unsigned int free_list_index(value_t size) {
  assert(0 <= size);
  return size >= FREE_LISTS_COUNT ? FREE_LISTS_COUNT - 1 : (unsigned int)size;
}

static void print_free_list(unsigned int fl_idx) {
  assert(fl_idx < FREE_LISTS_COUNT);

  value_t* block = free_list_heads[fl_idx];
  while (in_blocks(block)) {
    printf("%p (%d) -> ", block, addr_p_to_v(block));
    block = addr_v_to_p(block[0]);
  }

  printf("NULL \n");
  fflush(stdout);
}

static int is_free_list_empty(unsigned int fl_idx) {
  assert(fl_idx < FREE_LISTS_COUNT);
  return !in_blocks(free_list_heads[fl_idx]);
}

static value_t* pop_free_list(unsigned int fl_idx) {
  assert(fl_idx < FREE_LISTS_COUNT);
  assert(!is_free_list_empty(fl_idx));

  value_t* head = free_list_heads[fl_idx];
  free_list_heads[fl_idx] = addr_v_to_p(head[0]);
  head[0] = 0;
  return head;
}

static value_t* pop_first_fit_from_last_free_list(value_t size) {
  assert(0 <= size);
  if (is_free_list_empty(FREE_LISTS_COUNT - 1)) return NULL;

  value_t* prev = NULL;
  value_t* curr = free_list_heads[FREE_LISTS_COUNT - 1];

  do {
    if (get_block_size(curr) >= size) {
      if (prev == NULL) {
        free_list_heads[FREE_LISTS_COUNT - 1] = addr_v_to_p(curr[0]);
      } else {
        prev[0] = curr[0];
      }

      curr[0] = 0;
      return curr;
    }

    prev = curr;
    curr = addr_v_to_p(curr[0]);

  } while (in_blocks(curr));

  return NULL;
}

#define BEST_FIT_ERROR 1
static value_t* pop_best_fit_from_last_free_list(value_t size) {
  assert(0 <= size);
  if (is_free_list_empty(FREE_LISTS_COUNT - 1)) return NULL;

  int fit_exists = 0;

  value_t* best_fit_prev;
  value_t* best_fit;
  value_t best_fit_size;

  value_t* prev = NULL;
  value_t* curr = free_list_heads[FREE_LISTS_COUNT - 1];

  while (in_blocks(curr)) {
    value_t curr_size = get_block_size(curr);

    if (curr_size >= size) {
      if (fit_exists) {
        if (curr_size < best_fit_size) {
          best_fit_prev = prev;
          best_fit = curr;
          best_fit_size = curr_size;
          if (best_fit_size <= size + BEST_FIT_ERROR) break;
        }
      } else {
        fit_exists = 1;
        best_fit_prev = prev;
        best_fit = curr;
        best_fit_size = curr_size;
        if (best_fit_size <= size + BEST_FIT_ERROR) break;
      }
    }

    prev = curr;
    curr = addr_v_to_p(curr[0]);
  }

  if (!fit_exists) return NULL;

  if (best_fit_prev == NULL) {
    free_list_heads[FREE_LISTS_COUNT - 1] = addr_v_to_p(best_fit[0]);
  } else {
    best_fit_prev[0] = best_fit[0];
  }

  best_fit[0] = 0;
  return best_fit;
}

static value_t* pop_fit_from_free_lists(value_t size) {
  assert(0 <= size);

  unsigned int fl_idx = free_list_index(size);
  while (fl_idx < FREE_LISTS_COUNT && is_free_list_empty(fl_idx)) {
    fl_idx++;
  }

  if (fl_idx >= FREE_LISTS_COUNT) {
    return NULL;
  }

  if (fl_idx < FREE_LISTS_COUNT - 1) {
    return pop_free_list(fl_idx);
  }

  return pop_first_fit_from_last_free_list(size);
}

static void insert_to_correct_free_list(value_t* block) {
  assert(in_blocks(block));

  unsigned int fl_idx = free_list_index(get_block_size(block));
  assert(fl_idx < FREE_LISTS_COUNT);

  value_t* curr_head = free_list_heads[fl_idx];
  block[0] = addr_p_to_v(curr_head);
  free_list_heads[fl_idx] = block;
}

// Debug

static void print_state(int memory, int blocks, int free_lists) {
  if (memory) {
    printf("Printing Memory State: \n");
    printf("Memory start at %p, end at %p \n", memory_start, memory_end);
    printf("Bitmap start at %p \n", bitmap_start);
    printf("Heap start at %p (%d), end at %p (%d) \n", heap_start, heap_start_v, heap_end, heap_end_v);

    printf("\n");
  }

  if (blocks) {
    printf("Printing Heap Blocks: \n");
    int cnt = 1;
    value_t* block = heap_first_block;

    while (in_blocks(block)) {
      value_t size = get_block_size(block);
      tag_t tag = get_block_tag(block);

      printf("#%d: block at %p (%d), size %d, tag %d, bitmap %d \n"
            , cnt, block, addr_p_to_v(block), size, tag, bitmap_is_bit_set(block));
      
      cnt++;
      block += size + HEADER_SIZE;
    }

    printf("\n");
  }

  if (free_lists) {
    printf("Printing Freelists: \n");
    for (unsigned int i = 0; i < FREE_LISTS_COUNT; i++) {
      printf("#%u: ", i);
      print_free_list(i);
    }

    printf("\n");
  }

  fflush(stdout);
}

// Interfaces implementation

char* memory_get_identity() {
  return "mark & sweep garbage collector";
}

void memory_setup(size_t total_byte_size) {
  memory_start = malloc(total_byte_size);
  if (memory_start == NULL)
    fail("cannot allocate %zd bytes of memory", total_byte_size);
  memory_end = (char*)memory_start + total_byte_size;
}

void memory_cleanup() {
  assert(memory_start != NULL);
  free(memory_start);

  memory_start = memory_end = NULL;
  bitmap_start = NULL;
  heap_start = heap_end = NULL;
  heap_start_v = heap_end_v = 0;
  for (int l = 0; l < FREE_LISTS_COUNT; ++l)
    free_list_heads[l] = NULL;
}

void* memory_get_start() {
  return memory_start;
}

void* memory_get_end() {
  return memory_end;
}

void memory_set_heap_start(void* ptr) {
  assert(memory_start <= ptr && ptr < memory_end);

  const size_t bh_size =
    (size_t)((char*)memory_end - (char*)ptr) / sizeof(value_t);

  const size_t bitmap_size = (bh_size - 1) / (VALUE_BITS + 1) + 1;
  const size_t heap_size = bh_size - bitmap_size;

  bitmap_start = ptr;
  memset(bitmap_start, 0, bitmap_size * sizeof(value_t));

  heap_start = (value_t*)bitmap_start + bitmap_size;
  heap_end = heap_start + heap_size;
  assert(heap_end == memory_end);

  heap_start_v = addr_p_to_v(heap_start);
  heap_end_v = addr_p_to_v(heap_end);

  heap_first_block = heap_start + HEADER_SIZE;
  const value_t initial_block_size = (value_t)(heap_end - heap_first_block);
  heap_first_block[-1] = header_pack(tag_None, initial_block_size);
  heap_first_block[0] = 0;

  for (int l = 0; l < FREE_LISTS_COUNT - 1; ++l)
    free_list_heads[l] = memory_start;
  free_list_heads[FREE_LISTS_COUNT - 1] = heap_first_block;

  // print_state(1, 1, 1);
}

static value_t* split_block(value_t* block, tag_t tag, value_t size) {
  value_t block_size = get_block_size(block);
  assert(block_size >= size + HEADER_SIZE + MIN_BLOCK_SIZE);

  block[-1] = header_pack(tag, size);
  
  value_t* new_block = block + size + HEADER_SIZE;
  new_block[-1] = header_pack(tag_None, block_size - size - HEADER_SIZE);
  return new_block;
}

static value_t* allocate(tag_t tag, value_t size) {
  assert(0 <= size);

  size = real_size(size);
  value_t* fit_block = pop_fit_from_free_lists(size);
  if (fit_block == NULL) {
    return NULL;
  }

  value_t fit_block_size = get_block_size(fit_block);
  assert(fit_block_size >= size);

  if (fit_block_size >= size + HEADER_SIZE + MIN_BLOCK_SIZE) {
    value_t* new_block = split_block(fit_block, tag, size);
    insert_to_correct_free_list(new_block);
  } else {
    fit_block[-1] = header_pack(tag, fit_block_size);
  }

  bitmap_set_bit(fit_block);
  return fit_block;
}

static void mark(value_t* block) {
  if (!in_blocks(block)) return;
  if (!bitmap_is_bit_set(block)) return;

  bitmap_clear_bit(block);

  value_t block_size = get_block_size(block);
  for (value_t i = 0; i < block_size; i++) {
    if ((block[i] & 3) == 0) {
      value_t* next_block = addr_v_to_p(block[i]);
      if (in_blocks(next_block) && bitmap_is_bit_set(next_block)) {
        mark(next_block);
      }
    }
  }
}

static void coalesce_right(value_t* block) {
  assert(in_blocks(block));

  value_t block_size = get_block_size(block);
  value_t* right_block = block + block_size + HEADER_SIZE;
  value_t right_block_size = get_block_size(right_block);

  assert(in_blocks(right_block));
  assert(!bitmap_is_bit_set(block));
  assert(!bitmap_is_bit_set(right_block));

  block[-1] = header_pack(tag_None, block_size + HEADER_SIZE + right_block_size);
}

static void sweep() {
  // clear freelists
  for (unsigned int fl_idx = 0; fl_idx < FREE_LISTS_COUNT; fl_idx++) {
    value_t* block = free_list_heads[fl_idx];
    while (in_blocks(block)) {
      bitmap_set_bit(block);
      block = addr_v_to_p(block[0]);
    }

    free_list_heads[fl_idx] = memory_start;
  }

  // coalesce blocks
  value_t* prev_block_if_free = NULL;
  value_t* curr_block = heap_first_block;

  while (in_blocks(curr_block)) {
    value_t curr_block_size = get_block_size(curr_block);

    if (bitmap_is_bit_set(curr_block)) {
      bitmap_clear_bit(curr_block);

      if (prev_block_if_free) {
        coalesce_right(prev_block_if_free);
      } else {
        prev_block_if_free = curr_block;
      }
    } else {
      bitmap_set_bit(curr_block);

      if (prev_block_if_free) {
        insert_to_correct_free_list(prev_block_if_free);
        prev_block_if_free = NULL;
      }
    }

    curr_block += curr_block_size + HEADER_SIZE;
  }

  if (prev_block_if_free) {
    insert_to_correct_free_list(prev_block_if_free);
    prev_block_if_free = NULL;
  }
}

value_t* memory_allocate(tag_t tag, value_t size) {
  value_t* first_try = allocate(tag, size);

  if (first_try != NULL) {
    // print_state(0, 1, 1);
    memset(first_try, 0, size * sizeof(value_t));
    return first_try;
  }

  value_t* lb = engine_get_Lb();
  if (lb != memory_start) mark(lb);
  value_t* ib = engine_get_Ib();
  if (ib != memory_start) mark(ib);
  value_t* ob = engine_get_Ob();
  if (ob != memory_start) mark(ob);

  sweep();

  value_t* second_try = allocate(tag, size);
  if (second_try != NULL) {
    // print_state(0, 1, 1);
    memset(second_try, 0, size * sizeof(value_t));
    return second_try;
  }

  fail("\ncannot allocate %d words of memory, even after GC\n", size);
}

value_t memory_get_block_size(value_t* block) {
  return header_unpack_size(block[-1]);
}

tag_t memory_get_block_tag(value_t* block) {
  return header_unpack_tag(block[-1]);
}

#endif
