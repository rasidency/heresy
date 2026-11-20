#include <stdio.h>

int main(int argc, char **argv) {
    if (argc != 3 || argv[argc] != 0)
        return 9;
    if (argv[2][0] != 0)
        return 10;
    if (argv[1][0] >= 0 || argv[1][2] != 0)
        return 11;
    putchar(argv[0][0]);
    putchar(argv[1][0]);
    putchar(argv[1][1]);
    putchar('\n');
    return argc + 4;
}
