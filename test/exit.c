#include <stdio.h>
#include <stdlib.h>

static int stop(void) {
    putchar(65);
    exit(263);
}

int main(void) {
    int status = stop();
    putchar(66);
    return status;
}
