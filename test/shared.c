static int calls;

int left(void) { return calls++; }
int right(void) { return ++calls; }
int choose(void) { return (left() ?: right()) ?: right(); }

int main(void) {
  if (choose() != 2 || calls != 2) return 1;
  return choose() != 2 || calls != 3;
}
