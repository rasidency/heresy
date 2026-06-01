#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdfil.h>

struct Pair {
  int tag;
  long value;
  int *pointer;
};

int seed = 7;
long coefficients[3] = { 2, 3, 5 };
int *root = &seed;

int increment(int value) { return value + 1; }
int decrement(int value) { return value - 1; }

int main(int argc, char **argv) {
  int values[4] = { 1, 2, 3, 4 };
  char label[8] = "fil-c";
  struct Pair first = { 3, 42, &seed };
  struct Pair second;
  memcpy(&second, &first, sizeof(first));
  int (*operation)(int) = increment;
  printf("Layout: %lu %lu\n", sizeof(struct Pair), sizeof(values));
  printf("Initialisers: %d %ld %s %d\n", values[2], coefficients[2], label, *root);
  printf("Pointer copy: %d %ld %d\n", second.tag, second.value, *second.pointer);
  printf("Indirect call: %d %d\n", operation(41), increment != decrement);
  unsigned int bits = 4294967295U;
  printf("Wrapping: %u %lu\n", bits + 1U, (unsigned long)-1);
  printf("Signed division: %d %d %d\n", -7 / 3, -7 % 3, -8 >> 1);
  int counter = 0;
  int total = 0;
  for (int i = 0; i < 10; i++) {
    if (i == 3) continue;
    if (i == 8) break;
    total += i;
  }
  if (0 && ++counter) counter = 99;
  if (1 || ++counter) total++;
  printf("Control flow: %d %d\n", total, counter);
  printf("Pointer arithmetic: %ld %d\n", &values[3] - &values[0], *(2 + values));
  printf("Capabilities: %d %d %d\n", zhasvalidcap(&first), zhasvalidcap(0), zis_readonly("immutable"));
  char *buffer = calloc(8, 1);
  if (!buffer) return 2;
  printf("Rounded heap bounds: %ld\n", (char *)zgetupper(buffer) - (char *)zgetlower(buffer));
  memcpy(buffer, label, 6);
  printf("Byte copy: %s %lu\n", buffer, strlen(buffer));
  memset(buffer, 'x', 3);
  printf("Byte fill: %s\n", buffer);
  unsigned long blank = 0;
  memcpy(&second.pointer, &blank, sizeof(blank));
  printf("Cleared capability: %d\n", zhasvalidcap(second.pointer));
  printf("Empty copy: %d\n", memcpy(0, 0, 0) == 0);
  if (argc > 1) {
    argv[1][0] = 'F';
    printf("Mutable argument: %s\n", argv[1]);
  }
  free(buffer);
  return 256;
}
