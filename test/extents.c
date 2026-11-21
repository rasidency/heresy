#include <stdio.h>

struct Aligned {
    unsigned char first;
    long word;
};

int main(void) {
    int rows = 3;
    int columns[2] = {3, 4};
    unsigned long bytes = sizeof(int[rows++][2][columns[1]]);
    unsigned long alignment = _Alignof(int[rows++][2][columns[1]]);
    unsigned long record = sizeof(struct Aligned);
    unsigned long scalar = sizeof(rows++);
    unsigned long fixed = sizeof(short[2][3]);

    if (bytes != 96 || alignment != 4 || record != 16 || scalar != 4 || fixed != 12 || rows != 4)
        return 1;
    putchar('S');
    putchar('\n');
    return 5;
}
