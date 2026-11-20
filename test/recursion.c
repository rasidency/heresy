#include <stdio.h>
#include <stdlib.h>

static int forward(int count, unsigned char *payload);

static int repeat(int count, unsigned char *payload) {
    if (count == 0)
        return 0;
    putchar(*payload);
    return forward(count - 1, payload);
}

static int forward(int count, unsigned char *payload) {
    return repeat(count, payload);
}

int main(void) {
    unsigned char *payload = malloc(1);
    if (!payload)
        return 1;
    *payload = 65;
    int i = 0;
    while (i < 2) {
        repeat(1, payload);
        i = i + 1;
    }
    putchar(10);
    free(payload);
    return *payload;
}
