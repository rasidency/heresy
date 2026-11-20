#include <stdio.h>
#include <stdlib.h>

static unsigned char bytes[4] = {65, 66};
static int words[3] = {17, 67};
static unsigned char tail = 68;
static unsigned char *aliases[3] = {bytes, &tail};

int main(void) {
    if (aliases[2] != 0 || (aliases[0] == 0 && aliases[1] == 0))
        return 1;
    free(aliases[2]);
    putchar(bytes[0]);
    putchar(bytes[1]);
    words[2] = words[1];
    putchar(words[2]);
    unsigned char *last = aliases[1];
    putchar(*last);
    int pass = 0;
    while (pass < 2) {
        unsigned char buffer[2] = {70};
        if (pass == 0)
            buffer[1] = 90;
        else
            putchar(buffer[1] + 69);
        pass = pass + 1;
    }
    putchar(10);
    return bytes[3];
}
