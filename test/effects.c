#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int main(void) {
    unsigned char **buffer = malloc(24);
    unsigned char *payload = malloc(1);
    if (!buffer || !payload)
        return 1;
    *payload = 65;
    *(unsigned char **)((unsigned char *)buffer + 8) = payload;
    memmove(buffer, (unsigned char *)buffer + 8, 16);
    unsigned char *alias = *buffer;
    putchar(*alias);
    putchar(10);
    free(payload);
    return *alias;
}
