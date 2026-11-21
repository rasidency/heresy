#include <stdio.h>

static int mark(void) {
    putchar('A');
    return 1;
}

int main(int argc, char **argv) {
    unsigned int low = 0xffffffffU, high = 9, copied;
    int *alias;
    unsigned int rotated = 0x80000001U;
    unsigned char carry;
    __asm__ volatile ("addl $1, %0; adcl $0, %1" : "+&r"(low), "+r"(high) : : "cc");
    __asm__("movl %[source], %[target]" : [target] "=r"(copied) : [source] "r"(high));
    __asm__("roll $1, %0; setc %1" : "+r"(rotated), "=r"(carry) : : "cc");
    __asm__("stc; roll $32, %0; sbbl $0, %1" : "+&r"(rotated), "+r"(low) : : "cc");
    __asm__("nop\n\tpause" : : : "memory");
    __asm__("" : "=r"(alias) : "0"(&argc));
    if (low != 0xffffffffU || high != 10 || copied != high || rotated != 3 || carry != 1 || alias != &argc)
        return 5;
    int quotient = -1;
    quotient /= 2U;

    signed char byte = 127;
    signed char old = byte++;
    short word = -32768;
    short updated = --word;

    unsigned int mask = 128U;
    mask >>= 2L;
    mask ^= 3U;
    long long negative = -19LL;
    unsigned __int128 wide = (unsigned __int128)1 << 100U;
    unsigned __int128 check = (wide | 5) & (wide ^ 4);

    int zero = 0;
    int skipped = zero && 7 / zero;
    int result = mark() ? (putchar('B'), 7) : (putchar('X'), 8);
    int cells[5] = {3, 4, 5, 6, 7};
    int *base = &cells[0];
    int *current = base;
    current += 3L;
    int *last = current--;
    int *shifted = 1L + current;
    int *first = shifted - 3L;

    if (quotient != 2147483647 || old != 127 || byte != -128 || updated != 32767 || word != 32767)
        return 1;
    if (mask != 35U || ~mask != 4294967260U || negative / 4 != -4 || negative % 4 != -3)
        return 2;
    if ((negative >> 1LL) != -10 || (check >> 100) != 1 || (unsigned int)check != 4U || skipped)
        return 3;
    if (first != base || current >= last || last != shifted || last - base != 3 || base - last != -3 ||
        *first != 3 || current[1L] != 6)
        return 4;
    putchar('\n');
    if (argc > 1)
        return result / zero;
    return result;
}
