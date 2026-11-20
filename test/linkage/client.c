#include <stdio.h>

#include "scalar.h"

static unsigned char *alias = &shared;

static int adjust(int code) {
    return code + 1;
}

int main(void) {
    int local = adjust(*alias);
    int imported = remote(*alias);
    putchar(local);
    putchar(imported);
    putchar(10);
    return 0;
}
