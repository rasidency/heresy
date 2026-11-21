#include <stdarg.h>
#include <stdfil.h>
#include <stdio.h>

struct bundle {
    int *value;
    int code;
};

static int receive(int fault, ...) {
    va_list first;
    va_list second;
    va_start(first, fault);
    va_copy(second, first);
    int n = va_arg(first, int);
    int duplicate = va_arg(second, int);
    struct bundle bundle = va_arg(first, struct bundle);
    int *pointer = va_arg(first, int *);
    int tail = va_arg(first, int);
    unsigned __int128 wide = va_arg(first, unsigned __int128);
    unsigned long *words = zargs();
    if (n != -3 || duplicate != n || pointer != bundle.value || tail != 7 || wide != ((unsigned __int128)1 << 97))
        return 1;
    if (words[0] != (unsigned long)fault)
        return 2;
    if (!zcan_va_arg(first))
        putchar(bundle.code);
    putchar(64 + *pointer);
    putchar('\n');
    if (fault == 2)
        words[0] = 0;
    if (fault)
        return va_arg(first, int);
    va_end(second);
    va_end(first);
    return 0;
}

int main(int argc, char **argv) {
    int byte = 2;
    struct bundle bundle = { &byte, 65 };
    return receive(argc - 1, (signed char)-3, bundle, &byte, 7, (unsigned __int128)1 << 97);
}
