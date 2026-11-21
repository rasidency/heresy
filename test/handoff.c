#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>

static void *produce(void *argument) {
    unsigned char *byte = malloc(1);
    *byte = 65;
    return byte;
}

int main(int argc, char **argv) {
    pthread_t child;
    void *result;
    if (pthread_create(&child, 0, produce, 0) || pthread_join(child, &result))
        return 3;
    unsigned char *byte = result;
    putchar(*byte);
    putchar('\n');
    free(byte);
    if (argc > 1)
        return *byte;
    return 0;
}
