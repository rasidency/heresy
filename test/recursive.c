static unsigned long product(unsigned long count) {
  return count ? count * product(count - 1UL) : 1UL;
}

static unsigned long even(unsigned long count);

static unsigned long odd(unsigned long count) {
  return count ? even(count - 1UL) : 0UL;
}

static unsigned long even(unsigned long count) {
  if (count) return odd(count - 1UL);
  return 1UL;
}

int main(void) {
  return (int)(product(5UL) + odd(7UL));
}
