#include <stdio.h>
#include <stdlib.h>
#include <stdfil.h>
#include <stdarg.h>
#include <pthread.h>
#include <stdatomic.h>
#include <limits.h>
#include <complex.h>

struct Packet {
  long sequence;
  int *payload;
  float samples[2];
};

union SingleBits { float value; unsigned int bits; };
union DoubleBits { double value; unsigned long bits; };
union Message { struct Packet packet; long tag; };

struct Samples {
  unsigned long count;
  int readings[];
};

struct __attribute__((packed)) Bits {
  unsigned char tag;
  unsigned int mode : 3;
  signed int delta : 6;
  unsigned int : 0;
  unsigned long counter;
};

union Masks {
  unsigned int nibble : 4;
  unsigned long word;
};

int computed(int opcode) {
  static void *const dispatch[] = {&&add, &&multiply, &&finish};
  int value = 3;
  goto *dispatch[opcode];
add:
  value += 4;
  goto *dispatch[1];
multiply:
  value *= 5;
  goto *dispatch[2];
finish:
  return value;
}

void packed_values(void) {
  struct Bits value = {.tag = 9, .mode = 5, .delta = -4, .counter = 19};
  unsigned int mode = value.mode++;
  value.delta += 7;
  union Masks mask = {.word = 0xa0};
  mask.nibble = value.mode;
  printf("packed %lu %lu %u %u %u %d %lu %lx\n", sizeof(value), _Alignof(struct Bits),
         value.tag, mode, value.mode, value.delta, value.counter, mask.word);
  printf("dispatch %d %d %d\n", computed(0), computed(1), computed(2));
}

_Atomic int shared_count;
_Atomic(int *) shared_pointer;
_Thread_local int thread_local = 5;

void *count(void *argument) {
  int *output = argument;
  for (int i = 0; i < 4000; i++) atomic_fetch_add_explicit(&shared_count, 1, memory_order_relaxed);
  *output = ++thread_local;
  return output;
}

void concurrent_values(void) {
  pthread_t first;
  pthread_t second;
  int a = 0;
  int b = 0;
  if (pthread_create(&first, 0, count, &a) || pthread_create(&second, 0, count, &b)) exit(2);
  void *first_result = 0;
  void *second_result = 0;
  if (pthread_join(first, &first_result) || pthread_join(second, &second_result)) exit(2);
  printf("threads %d %d %d %d %d %d\n", atomic_load(&shared_count),
         a, b, thread_local, first_result == &a && second_result == &b, pthread_equal(first, second));
}

struct Scoped { int prefix; long *link; int tail; };
typedef struct { int key; unsigned char value; } Anonymous;
static const Anonymous fixed = {1, 3};
struct Nested { struct { int value; } head; union { short narrow; int wide; }; };

void scoped_values(struct Scoped *outer) {
  typedef struct Scoped Outer;
  struct Scoped { unsigned flags : 9; long value; };
  struct Scoped local = {257, 12};
  Outer copy = *outer;
  Anonymous pair[2] = {{1, 7}, {14, 3}};
  struct Nested nested = {{5}, {.wide = 21}};
  printf("scopes %lu %lu %d %u %ld %d %d %d %d\n",
         sizeof *outer, sizeof local, outer->tail + copy.tail, local.flags, local.value,
         pair[1].key + pair[0].value, nested.head.value, nested.wide, zis_readonly((void*)&fixed));
  {
    struct Scoped { unsigned char bytes[3]; };
    struct Scoped inner = {{6}};
    printf("inner %lu %u\n", sizeof inner, (unsigned)inner.bytes[0]);
  }
}

#define KEEP_REGISTER(value) __asm__("" : "+r"(value))

void assembly_values(void) {
  int values[2] = {41, 8};
  int index = 0;
  int *pointer = values;
  __asm__ __volatile__("" : "+r"(values[index++]) : : "memory");
  KEEP_REGISTER(pointer);
  __asm__ __volatile__("nop\n\tpause\n\tmfence" : : : "memory", "cc");
  unsigned int word = 0xffffffffU;
  __asm__("addl $5, %0\n\txorl $3, %0\n\tnegl %0" : "+r"(word) : : "cc");
  printf("asm %d %d %d %x\n", index, zhasvalidcap(pointer), values[0], word);
}

struct AtomicCap { int *p; };
struct AtomicWord { int *p; long tag; };
struct AtomicWide { int *p; long tag, tail; };
struct AtomicTiny { unsigned char bytes[3]; };

void aggregate_atomics(void) {
  int a = 7, b = 9;
  _Atomic(struct AtomicCap) cap;
  atomic_init(&cap, ((struct AtomicCap){&a}));
  struct AtomicCap previous = atomic_exchange(&cap, ((struct AtomicCap){&b}));
  struct AtomicCap current = atomic_load(&cap);
  printf("atomic cap %d %d\n", *previous.p, *current.p);

  _Atomic(struct AtomicWord) word = (struct AtomicWord){&a, 1};
  struct AtomicWord *ordinary = (struct AtomicWord*)&word;
  int preserved = zhasvalidcap(ordinary->p);
  struct AtomicWord lost = atomic_exchange(&word, ((struct AtomicWord){&b, 2}));
  struct AtomicWord fresh = atomic_load(&word);
  printf("atomic word %d %d %ld %d %ld\n",
         preserved, zhasvalidcap(lost.p), lost.tag, zhasvalidcap(fresh.p), fresh.tag);

  struct AtomicWide wide = {&a, 3, 4}, replacement = {&b, 5, 6}, old;
  __atomic_exchange(&wide, &replacement, &old, __ATOMIC_SEQ_CST);
  int won = __atomic_compare_exchange(&wide, &old, &replacement, 0, __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST);
  printf("atomic wide %d %ld %ld %d\n", *old.p, old.tag, old.tail, won);

  _Atomic(struct AtomicTiny) tiny;
  unsigned char *bytes = (unsigned char*)&tiny;
  bytes[3] = 171;
  atomic_init(&tiny, ((struct AtomicTiny){{1, 2, 3}}));
  unsigned char cleared = bytes[3];
  bytes[3] = 171;
  struct AtomicTiny expected = {{9, 8, 7}};
  won = atomic_compare_exchange_strong(&tiny, &expected, ((struct AtomicTiny){{4, 5, 6}}));
  printf("atomic tiny %lu %lu %u %u %d %u\n", sizeof tiny, _Alignof(_Atomic(struct AtomicTiny)),
         (unsigned)cleared, (unsigned)bytes[3], won, (unsigned)expected.bytes[0]);
}

struct Synchronised {
  pthread_mutex_t mutex;
  pthread_cond_t ready;
  pthread_cond_t gate;
  int arrived;
  int open;
  int total;
};

void *synchronised_worker(void *argument) {
  struct Synchronised *state = argument;
  pthread_mutex_lock(&state->mutex);
  ++state->arrived;
  pthread_cond_signal(&state->ready);
  while (!state->open) pthread_cond_wait(&state->gate, &state->mutex);
  state->total += 7;
  pthread_mutex_unlock(&state->mutex);
  return argument;
}

void synchronised_values(void) {
  struct Synchronised state = {
    .mutex = PTHREAD_MUTEX_INITIALIZER,
    .ready = PTHREAD_COND_INITIALIZER,
    .gate = PTHREAD_COND_INITIALIZER
  };
  pthread_t first, second;
  pthread_mutex_lock(&state.mutex);
  int busy = pthread_mutex_trylock(&state.mutex);
  pthread_create(&first, 0, synchronised_worker, &state);
  pthread_create(&second, 0, synchronised_worker, &state);
  while (state.arrived < 2) pthread_cond_wait(&state.ready, &state.mutex);
  state.open = 1;
  pthread_cond_broadcast(&state.gate);
  pthread_mutex_unlock(&state.mutex);
  pthread_join(first, 0);
  pthread_join(second, 0);
  int ready = pthread_cond_destroy(&state.ready);
  int gate = pthread_cond_destroy(&state.gate);
  int mutex = pthread_mutex_destroy(&state.mutex);
  printf("pthread sync %d %d %d %d %d %d\n", state.arrived, state.total, busy, ready, gate, mutex);
}

void atomic_values(void) {
  _Atomic int wrap = INT_MAX;
  int before = atomic_fetch_add(&wrap, 1);
  int expected = 9;
  int miss = atomic_compare_exchange_strong(&wrap, &expected, 17);
  int hit = atomic_compare_exchange_strong(&wrap, &expected, 23);
  int v[3] = {40, 61, 71};
  atomic_store(&shared_pointer, v);
  unsigned long *payload = (unsigned long *)&shared_pointer;
  *payload += sizeof(int);
  int *unmoved = atomic_load(&shared_pointer);
  int *old = atomic_fetch_add(&shared_pointer, 1);
  int *after = atomic_exchange(&shared_pointer, v + 2);
  printf("atomics %d %d %d %d %d %d %d %ld %d %d\n", before, expected, miss, hit,
         atomic_load(&wrap), *unmoved, zhasvalidcap(old), (char *)old - (char *)v,
         *after, *atomic_load(&shared_pointer));
}

long double extended_value(int named, ...) {
  va_list list;
  va_start(list, named);
  long double result = va_arg(list, long double);
  int following = va_arg(list, int);
  va_end(list);
  void *area = zargs();
  printf("extended layout %lu %lu %ld %d\n", sizeof(result), _Alignof(long double),
         (char*)zgetupper(area) - (char*)area, following);
  return result;
}

void extended_values(void) {
  long double a = extended_value(2, 0x1.0000000000000002p0L, 7);
  long double difference = a - 1.0L;
  long double smallest = 0x1p-16445L;
  long double zero = 0.0L;
  long double not_a_number = zero / zero;
  long double inf = 1.0L / zero;
  printf("extended %.22Lf %d %d %d %d %d %.1Lf\n", a, a > 1.0L, (double)a == 1.0,
         difference == 0x1p-63L, smallest != 0.0L && smallest / 2.0L == 0.0L,
         not_a_number != not_a_number && inf > a, -0.0L);
}

typedef unsigned __int128 Wide;

Wide wide_argument(int a, int b, ...) {
  va_list list;
  va_start(list, b);
  Wide value = va_arg(list, Wide);
  int tail = va_arg(list, int);
  va_end(list);
  printf("wide argument %lu %lu %d\n", sizeof(value), _Alignof(Wide), a + b + tail);
  return value;
}

void wide_slot(int a, ...) {
  unsigned long *words = zargs();
  va_list list;
  va_start(list, a);
  Wide value = va_arg(list, Wide);
  va_end(list);
  printf("wide slot %lu %lu %lu %lu %lu\n", words[1], words[2], words[3],
         (unsigned long)value, (unsigned long)(value >> 64));
}

void wide_values(void) {
  Wide value = ((Wide)345 << 64) + 189;
  Wide roundtrip = wide_argument(2, 5, value, 7);
  Wide overflow = (Wide)-1;
  overflow += roundtrip;
  __int128 signed_value = -((__int128)50 << 70);
  printf("wide %d %d %ld %.0f\n", roundtrip == value, overflow == value - 1,
         (long)(signed_value >> 70), (double)((__int128)-3));
  wide_slot(9, value, 74);
}

void complex_arguments(int named, ...) {
  va_list list;
  va_start(list, named);
  float _Complex f = va_arg(list, float _Complex);
  double _Complex d = va_arg(list, double _Complex);
  long double _Complex x = va_arg(list, long double _Complex);
  va_end(list);
  void *area = zargs();
  printf("complex args %ld %.1f %.1f %.1f %.1f %.1Lf %.1Lf\n",
         (char*)zgetupper(area) - (char*)area,
         __real__ f, __imag__ f, __real__ d, __imag__ d, __real__ x, __imag__ x);
}

void complex_values(double zero) {
  double infinity = 1.0 / zero;
  double nan = zero / zero;
  double _Complex z = CMPLX(1.5, -2.25);
  double _Complex w = CMPLX(7.25, 8.5);
  double _Complex q = z;
  q *= w;
  q /= w;
  double _Complex invalid = CMPLX(nan, 1.0);
  double _Complex limit = CMPLX(infinity, nan) * w;
  double _Complex inverse = w / CMPLX(infinity, nan);
  double _Complex singular = w / CMPLX(-zero, zero);
  float _Complex f = q;
  __imag__ f = -0.0f;
  long double _Complex extended = CMPLXL(0x1.0000000000000002p0L, -2.0L) * CMPLXL(4.0L, -1.0L);
  printf("complex math %.8f %.8f %d %d %d %d %d %d %d %d\n",
         __real__ q, __imag__ q, z == w, invalid != invalid, !!invalid,
         __real__ limit > 0.0, __imag__ limit > 0.0, inverse == CMPLX(0.0, 0.0),
         __real__ singular < 0.0 && __imag__ singular < 0.0, 1.0f / __imag__ f < 0.0f);
  printf("complex extended %.21Lf %.5Lf\n", __real__ extended, __imag__ extended);
  complex_arguments(17, f, w, extended);
}

int adjusted_rows(int n, int m, int a[n++][m++], int b[static n++]) {
  printf("array args %d %d %lu\n", n, m, sizeof *a);
  return a[1][2] + b[0];
}

int pointer_rows(int n, int (*a)[n++]) {
  return n + sizeof(*a) + a[1][2];
}

void variable_array_values(int n, int m) {
  int matrix[n++][m++];
  int writes = 0;
  for (int i = 0; i < n - 1; i++)
    for (int j = 0; j < m - 1; j++) {
      matrix[i][j] = i * 17 + j;
      ++writes;
    }
  int row = 0;
  long sub = sizeof(matrix[row++]);
  long span = sizeof matrix;
  int (*cursor)[m - 1] = matrix;
  cursor++;
  int k = 2;
  long type_size = sizeof(short[++k][4]);
  printf("vla %d %d %d %d %ld %ld %d %ld %d %ld %d\n", n, m, writes, row, span, sub,
         (*(matrix + 1))[2], (matrix + 1) - matrix, (*cursor)[4], type_size, k);
  int a = adjusted_rows(n - 1, m - 1, matrix, *matrix);
  int b = pointer_rows(m - 1, matrix);
  typedef int Row[n++];
  Row copy;
  n = 50;
  copy[2] = 6;
  printf("shape %lu %lu %d %d %d %d\n", sizeof(Row), sizeof copy, n, copy[2], a, b);
}

struct Packet transform(struct Packet packet, double real) {
  packet.sequence++;
  *packet.payload += 2;
  packet.samples[0] += real;
  packet.samples[1]++;
  return packet;
}

struct Packet retrieve(struct Packet *pointer) {
  return *pointer;
}

union Message relay(union Message message) {
  message.packet.sequence += 9;
  return message;
}

double ratio(float numerator, double denominator) {
  return numerator / denominator;
}

int report(const char *format, ...) {
  va_list args;
  va_start(args, format);
  int count = vprintf(format, args);
  va_end(args);
  return count;
}

void padded(int named, ...) {
  va_list args;
  va_start(args, named);
  int first = va_arg(args, int);
  int second = va_arg(args, int);
  int padded = zcan_va_arg(args);
  long last = padded ? va_arg(args, long) : -1;
  int after = zcan_va_arg(args);
  va_end(args);
  void *area = zargs();
  printf("padding %d %d %d %ld %d %ld\n", first, second, padded, last, after,
         (char*)zgetupper(area) - (char*)area);
}

long read_variadic(va_list list) {
  int integer = va_arg(list, int);
  double real = va_arg(list, double);
  int *pointer = va_arg(list, int *);
  struct Packet packet = va_arg(list, struct Packet);
  return integer + (long)(real * 4.0) + *pointer + packet.sequence + *packet.payload;
}

long variadic(struct Packet named, int tag, ...) {
  va_list list;
  va_list copy;
  va_start(list, tag);
  va_copy(copy, list);
  long first = read_variadic(list);
  long second = read_variadic(copy);
  int more = zcan_va_arg(copy);
  va_end(copy);
  va_end(list);
  void *area = zargs();
  printf("varargs %ld %ld %d %d %ld %lu\n", first, second, more, zis_readonly(area),
         (char*)zgetupper(area) - (char*)area, sizeof(va_list));
  return named.sequence + tag;
}

int payload = 40;
const int *table = (const int[]){5, 7, 11};

int jumps(void) {
  int *previous = 0;
  int *prior_literal = 0;
  int iteration = 0;
  int total = 0;
  goto begin;
again:
  {
    int local[] = {++iteration, 0};
    int *literal = (int[]){iteration + 4, 0};
    if (previous) total += (*previous == iteration) + (prior_literal == literal) + local[1] + literal[1];
    if (iteration == 1) { local[1] = 50; literal[1] = 50; }
    previous = local;
    prior_literal = literal;
    total += literal[0];
    if (iteration < 3) goto again;
  }
  return total;
begin:
  goto again;
}

int cases(int count) {
  int total = 0;
  int position = 0;
  switch (count) {
    case 0:
      do {
        total += 10;
        case 1: total++;
        case 2: position++;
      } while (position < 3);
      break;
    default: total = 70;
  }
  return total;
}

int main(int argc, char **argv) {
  (void)argv;
  struct Packet original = {11, &payload, {0.25f, 1.5f}};
  struct Packet copy = original;
  struct Packet (*apply)(struct Packet, double) = transform;
  copy = apply(copy, 2.25);
  int same = copy.payload == original.payload;
  printf("copies %ld %ld %d %d %d %d\n", original.sequence, copy.sequence, same,
         *original.payload, (int)(original.samples[0] * 4), (int)(copy.samples[0] * 4));
  struct Packet *literal = &(struct Packet){19, &payload, {2.0f, -3.0f}};
  union Message message = {.packet = retrieve(literal)};
  message = relay(message);
  long sequence = (argc ? message.packet : copy).sequence;
  printf("members %ld %d %d\n", sequence, *retrieve(literal).payload,
         (int)retrieve(literal).samples[1]);
  union SingleBits rounded = {.value = 16777216.0f + (float)argc};
  union SingleBits subnormal = {.value = 0x1p-149f};
  union DoubleBits negative_zero = {.value = -0.0};
  double zero = (double)(argc - 1);
  double inf = ratio(1.0f, zero);
  double nan = ratio(0.0f, zero);
  long truncated = -5;
  truncated += 1.75;
  printf("ieee %x %x %lx %d %d %d %d %ld\n", rounded.bits, subnormal.bits,
         negative_zero.bits, !negative_zero.value, inf > 1.0, nan != nan, nan < 1.0, truncated);
  printf("decimal %09.2f %.2f %.0f %.0f %f %09.2f\n", -3.5, 2.675, 2.5, 3.5,
         negative_zero.value, inf);
  int *freed = malloc(sizeof(int));
  if (!freed) return 2;
  struct Packet dangling = {0, freed, {0.0f, 0.0f}};
  struct Packet alias = dangling;
  free(freed);
  printf("liveness %d %d\n", zhasvalidcap(dangling.payload), zhasvalidcap(alias.payload));
  printf("control %d %d %d %d %d %d %d\n", jumps(), cases(0), cases(1), cases(2), cases(3),
         table[2], zis_readonly((void*)table));
  long named = variadic(original, 7, (unsigned char)3, 1.25f, &payload, copy);
  struct Samples *samples = malloc(sizeof(*samples) + sizeof(int) * 2);
  if (!samples) return 2;
  samples->count = 2;
  samples->readings[1] = 17;
  printf("flexible %ld %lu %lu %u %d\n", named, sizeof(*samples), _Alignof(struct Samples),
         (unsigned)samples->count, samples->readings[1]);
  free(samples);
  int count = report("report %s %d %.2f\n", "slots", 13, 2.675);
  printf("count %d\n", count);
  padded(2, 5, 6);
  packed_values();
  struct Scoped scoped = {0, 0, 8};
  scoped_values(&scoped);
  assembly_values();
  atomic_values();
  aggregate_atomics();
  concurrent_values();
  synchronised_values();
  extended_values();
  wide_values();
  complex_values(zero);
  variable_array_values(3, 5);
  return 0;
}
