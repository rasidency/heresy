#include <stdio.h>
#include <stdlib.h>
#include <stdfil.h>

int main(void) {
  long *owner = malloc(3 * sizeof(long));
  if (!owner) return 2;
  owner[0] = 17;
  owner[1] = 42;
  owner[2] = 99;
  long *alias = owner + 1;
  printf("Alias before free: %ld\n", *alias);
  printf("Alias capability before free: %d\n", zhasvalidcap(alias));
  free(owner);
  printf("Alias capability after free: %d\n", zhasvalidcap(alias));
  puts("Reading the interior alias after free");
  printf("Alias after free: %ld\n", *alias);
  return 0;
}
