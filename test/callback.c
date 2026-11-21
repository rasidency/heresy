#include <string.h>

static int increment(int value) {
    return value + 1;
}

static int decrement(int value) {
    return value - 1;
}

static int apply(int (*operation)(int), int value) {
    return operation(value);
}

static int row(int (*rows)[2]) {
    if ((unsigned char *)(rows + 1) - (unsigned char *)rows != 2 * sizeof(int))
        return 0;
    return rows[0][1];
}

int main(int argc, char **argv) {
    int values[2] = {1, 41};
    int value = row(&values);
    int (*selected)(int) = argc > 1 ? decrement : increment;
    int (*copy)(int);
    memcpy(&copy, &selected, sizeof copy);
    if (argc > 3) {
        unsigned char *bytes = (unsigned char *)&copy;
        bytes[0] ^= 1;
    } else if (argc > 2) {
        copy = 0;
    }
    return apply(copy, value);
}
