#include <stdio.h>

struct Payload { int *pointer; long value; };

extern int shared;
extern _Thread_local int current;
struct Payload acquire(void);

static int counter = 3;
static int advance(void) { return ++counter; }
int *reference = &shared;

int main(void) {
  struct Payload result = acquire();
  int local = advance();
  printf("linkage %d %d %ld %d %d\n", local, *reference, result.value, *result.pointer, current);
  return 0;
}
