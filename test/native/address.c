#include <stdio.h>

int main(void) {
    int value = 1;
    int *pointer = &value;
    unsigned char *bytes = (unsigned char *)&pointer;
    printf("%d %u\n", bytes[5] != 0, (unsigned)bytes[4]);
    return 0;
}
