#include <stdio.h>
#include <stdlib.h>
#include <stdfil.h>

int main(int argc, char **argv) {
  unsigned char *buffer = malloc(16);
  if (!buffer) return 2;
  for (int i = 0; i < 16; i++) buffer[i] = (unsigned char)(i + 65);
  int index = argc == 2 && argv[1][0] == '1' ? 16 : 15;
  printf("Sixteen-byte buffer, reading offset %d\n", index);
  printf("Value: %c\n", buffer[index]);
  free(buffer);
  return 0;
}
