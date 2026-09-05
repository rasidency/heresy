int main(void) {
  return (int)((0xffffffffffffffffUL + 1UL) ? 0UL : (0x80000125UL ^ 0x100UL));
}
