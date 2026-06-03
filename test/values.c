#include <stdio.h>
#include <stdlib.h>
#include <stdfil.h>
#include <stdarg.h>
#include <pthread.h>
#include <stdatomic.h>
#include <limits.h>

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
  atomic_values();
  concurrent_values();
  extended_values();
  variable_array_values(3, 5);
  return 0;
}
