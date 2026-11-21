#include <stdarg.h>
#include <stdio.h>

union Extended {
    long double value;
    unsigned __int128 bits;
};

static long double receive(int first, ...) {
    va_list args;
    va_start(args, first);
    long double value = va_arg(args, long double);
    int tail = va_arg(args, int);
    va_end(args);
    if (tail != 73)
        return 0.0L;
    return value;
}

static void inspect(long double value) {
    union Extended cell;
    cell.value = value;
    unsigned __int128 bits = cell.bits;
    printf("%lx %lx\n", (unsigned long)(bits >> 64) & 65535UL, (unsigned long)bits);
}

union Single {
    float value;
    unsigned int bits;
};

union Double {
    double value;
    unsigned long bits;
};

static float single(float value) {
    return value;
}

static double real(int tag, ...) {
    va_list args;
    va_start(args, tag);
    double value = va_arg(args, double);
    va_end(args);
    return value;
}

int main(void) {
    inspect(receive(1, 0x1.0000000000000002p0L, 73));
    inspect(receive(1, 0x1p-16445L, 73));
    inspect(receive(1, 0x1.fffffffffffffffep16383L, 73));
    union Single small;
    union Double normal;
    small.value = single(0x1p-149f);
    normal.value = real(1, 0x1.0000000000001p0);
    printf("%x %lx\n", small.bits, normal.bits);
    int count = -3;
    double promoted = count++ ?: 0.5;
    normal.bits = 0x8000000000000000UL;
    printf("%.1f %d %06.1f %.0f %.0f\n", promoted, count, normal.value, 2.5, 3.5);
    normal.bits = 0x7ff0000000000000UL;
    printf("%06F\n", normal.value);
    return 0;
}
