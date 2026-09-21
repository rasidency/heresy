int main(void) {
  unsigned long total = 0xffffffffffffffffUL, phase = total + 1UL;
  if (phase) {
    return (int)91UL;
  } else {
    unsigned long total = 0x125UL;
    (total) = total ^ 0x100UL;
    phase = total;
  }
  if (total ^ 0xffffffffffffffffUL) return (int)92UL;
  total = phase;
  unsigned long count = 27UL;
  while (count) {
    unsigned long step = 1UL;
    while (step) {
      total = total + step;
      step = step - 1UL;
    }
    count = count - 1UL;
  }
  total = total - 27UL;
  if (total - 37UL) return (int)93UL;
  while (total) return (int)(total | 0x80000000UL);
  return (int)94UL;
}
