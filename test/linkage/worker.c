#include <pthread.h>

struct Payload { int *pointer; long value; };

int shared = 17;
_Thread_local int current = 7;
static int counter = 41;
static int advance(void) { return ++counter; }
static pthread_t (*const self)(void) = pthread_self;

int thread_identity(void) {
  return self() != (pthread_t)0;
}

struct Payload acquire(void) {
  ++shared;
  current += 2;
  return (struct Payload){&shared, advance()};
}
