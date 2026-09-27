static unsigned long seed(void) {
  return 4UL;
}

static unsigned long weight(unsigned long first, unsigned long second, unsigned long third);

static unsigned long finish(unsigned long value) {
  return value ^ weight(1UL, 2UL, 3UL);
}

int main(void) {
  unsigned long total = 1UL, count = 2UL;
  while (count) {
    total = weight(total, seed(), count);
    count = count - 1UL;
  }
  return (int)(finish(total) | 0x80000000UL);
}

static unsigned long weight(unsigned long first, unsigned long second, unsigned long third) {
  return first * 3UL + second * 5UL + third * 7UL;
}
