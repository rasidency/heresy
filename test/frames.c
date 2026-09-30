static unsigned long accumulate(unsigned long start, unsigned long count) {
  unsigned long result = start;
  while (count) {
    result = result + count;
    count = count - 1UL;
  }
  if (result) return result;
  return 17UL;
}

static unsigned long combine(unsigned long start) {
  unsigned long first = accumulate(start, 4UL);
  unsigned long second = accumulate(start + 2UL, 2UL);
  return (first * 3UL) ^ second;
}

int main(void) {
  unsigned long start = 3UL;
  return (int)(combine(start) + start);
}
