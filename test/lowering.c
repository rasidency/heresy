#include <complex.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdfil.h>
#include <string.h>

enum Action { Begin = -3, Advance, Finish = 8 };
enum Wide { Large = 0x100000000UL, Larger };
enum Small { Empty, Ready };
typedef enum { Cold = 2, Hot } Temperature;
typedef enum Wide Widths[2];
typedef int Row[3];
union Word { unsigned long bits; int *pointer; unsigned char bytes[8]; };
int global = 42;
union Word initial = {.pointer = &global};
int increment(int value);
int decrement(int value);
int (*const immutable[2])(int) = {increment, decrement};
int (*mutable[2])(int) = {decrement, increment};
typedef int (*Transform)(int);
const Transform aliased[2] = {increment, decrement};

int increment(int value) { return value + 1; }
int decrement(int value) { return value - 1; }
int doubleréel(int value) { return value * 2; }

void closure(int distances[4][4]) {
  for (int via = 0; via < 4; via++)
    for (int from = 0; from < 4; from++)
      for (int to = 0; to < 4; to++)
        if (distances[from][via] + distances[via][to] < distances[from][to])
          distances[from][to] = distances[from][via] + distances[via][to];
}

int classify(int value) {
  int total = 0;
  switch (value) {
    default: total = 40; break;
    case -3: total++;
    case -2: case 0: total += 2; break;
    case 3 ... 5: total += 8; break;
    case 9: return 71;
  }
  do {
    total--;
    if (total > 5) continue;
    break;
  } while (total > 0);
  return total;
}

int loops(void) {
  int total = 0;
  for (int i = 0; i < 5; i++) {
    switch (i) {
      case 0: total++; continue;
      case 1: total += 2; break;
      default: switch (i) { case 3: total += 3; break; default: total += 4; }
    }
    total += 10;
  }
  int conditions = 0;
  do { if (conditions == 2) break; } while (++conditions < 9);
  return total + conditions;
}

int main(int argc, char **argv) {
  int distances[4][4] = {{0,3,99,10},{99,0,2,99},{99,99,0,1},{7,99,99,0}};
  closure(distances);
  printf("paths %d %d %d %lu\n", distances[0][3], distances[3][1], distances[3][2], sizeof(*distances));
  Row rows[2] = {{1,2,3},{4,5,6}};
  Row *row = rows;
  Row **indirect = &row;
  (*indirect)++;
  (*row)[2] = 9;
  int cube[2][3][4] = {[1][2][3] = 71};
  int (*functions[2][2])(int) = {{increment,decrement},{decrement,increment}};
  printf("arrays %d %d %d %lu %lu %lu\n", rows[1][2], cube[1][2][3], functions[1][1](4), sizeof(*row), sizeof(cube), sizeof(functions));
  union Word word = {.bits = 0x102};
  printf("union %u %u %lu ", word.bytes[0], word.bytes[1], sizeof(union Word));
  word.pointer = &global;
  word.bytes[0] ^= 1;
  int live = zhasvalidcap(word.pointer);
  word.bytes[0] ^= 1;
  printf("%d %d %d\n", live, *word.pointer, *initial.pointer);
  printf("readonly %d %d %d %d\n", zis_readonly((void*)immutable), zis_readonly(mutable), zis_readonly((void*)aliased), immutable[0](4));
  enum Action action = Advance;
  enum Small small = (enum Small)-1;
  enum { LocalNegative = -7, LocalNext } local = LocalNext;
  enum { Absent, Present } anonymous[2] = {Absent, Present};
  Widths widths = {Large, Larger};
  Temperature temperature = Hot;
  printf("enum %d %d %d %d %d %lu %lu\n", action, small < Empty, local, anonymous[1], temperature, widths[1], sizeof(widths));
  printf("switch");
  for (int i = -4; i < 11; i++) printf(" %d", classify(i));
  printf(" %d\n", loops());
  int effects = 0, selected = 3;
  _Generic((++effects), int:selected, default:effects) = 12;
  int evaluated = _Generic((++effects), int:({
    int subtotal = 0;
    for (int i = 0; i < 4; ++i) {
      int token = ({
        if (i == 2) continue;
        if (i == 3) break;
        i + 10;
      });
      subtotal += token;
    }
    switch (subtotal) {
      case 21: subtotal += selected; break;
      default: return 91;
    }
    subtotal;
  }), default:99);
  printf("generic %d %d %d\n", effects, selected, evaluated);
  int shared = 0;
  int fallback = shared++ ?: ++shared;
  double promoted = shared++ ?: 0.5;
  int *missing = 0;
  int *retained = (missing ?: &shared) ?: &fallback;
  printf("conditional %d %.1f %d %d\n", fallback, promoted, shared, retained == &shared);
  int nested = ({ int value = 2; goto finish; value = 100; finish: value + 1; });
  printf("nested label %d\n", nested);
  int inline_field = ((struct {char c; int value;}){1, 8}).value;
  unsigned int inline_bits = ((struct {unsigned :1; unsigned :0; unsigned value:3;}){.value=5}).value;
  int inline_member = ((struct {struct {int member;};}){.member=22}).member;
  printf("inline records %d %u %d %d %lu\n", inline_field, inline_bits, inline_member,
         (int)cimag(CMPLX(4.0, 2.0)), sizeof(struct {char c; long value;}));
  typedef struct { long value; } Cell;
  Cell outside = {71};
  Cell *outer = &outside;
  {
    typedef struct { unsigned char byte; } Cell;
    Cell values[2] = {{21}, {39}};
    typedef Cell (*Row)[2];
    Row row = &values;
    printf("scoped typedefs %lu %lu %ld %u\n",
           sizeof(*outer), sizeof(*row), outer->value, (unsigned)(*row)[1].byte);
  }
  switch (1) {
    int skipped = 99;
    case 0: skipped = 71;
    case 1: printf("skipped %d\n", skipped); break;
  }
  FILE *file = fopen("build/données.bin", "wb");
  if (!file) return 2;
  const char *text = "capacité λ";
  long count = 12;
  if (fwrite(text, 1, (unsigned long)count, file) != (unsigned long)count || fclose(file) != 0) return 2;
  file = fopen("build/données.bin", "rb");
  if (!file) return 2;
  char restored[16];
  if (fread(restored, 1, (unsigned long)count, file) != (unsigned long)count || fclose(file) != 0) return 2;
  restored[count] = 0;
  printf("unicode %d %s\n", doubleréel(21), restored);
  unsigned long size = 67108880UL;
  unsigned char *large = malloc(size);
  if (!large) return 2;
  large[0] = 7;
  large[size - 1] = 9;
  printf("allocation %u %u %ld\n", large[0], large[size - 1], (char*)zgetupper(large) - (char*)zgetlower(large));
  free(large);
  int width = printf("%05000d", 7);
  printf("\nwidth %d\n", width);
  if (argc > 1) printf("argument %lu %s\n", strlen(argv[1]), argv[1]);
  return 0;
}
