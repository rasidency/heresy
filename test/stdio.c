#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static char *message(void) {
    return "A\0hidden";
}

int main(int argc, char **argv) {
    char padded[6] = "xy";
    char exact[16] = "abcdefghijklmnop";
    char *text = message();
    char *again = message();
    if (text != again || padded[5] != 0 || exact[1] != 'b')
        return 1;

    int difference = strcmp(exact + 15, text);
    if (difference != 47 || strlen(text) != 1)
        return 3;
    unsigned char *buffer = calloc(2, 2);
    if (!buffer || buffer[0] != 0 || buffer[3] != 0)
        return 4;
    void *destination = memset(buffer + 1, 321, 2);
    if (destination != buffer + 1 || buffer[0] != 0 || buffer[1] != 65 || buffer[2] != 65 || buffer[3] != 0)
        return 5;
    free(buffer);

    int count = printf("%04d %02X %hhu %lo %% %3s %c\n", -7, 10u, 257u, 8ul, text, '!');
    if (count != 21)
        return 2;
    if (argc > 1)
        return printf("%s", exact);
    puts(padded);
    return 0;
}
