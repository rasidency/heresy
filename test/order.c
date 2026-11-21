#include <stdio.h>

struct Pair {
    int left;
    int right;
};

static int cell;
static struct Pair pair;
static struct Pair source = { 4, 2 };

static int *base(void) {
    putchar('B');
    return &cell;
}

static int indexof(void) {
    putchar('I');
    return 0;
}

static int value(void) {
    putchar('V');
    return 3;
}

static struct Pair *place(void) {
    putchar('P');
    return &pair;
}

static struct Pair record(void) {
    putchar('R');
    return source;
}

int main(void) {
    base()[indexof()] = value();
    base()[indexof()] += value();
    *place() = record();
    printf(" %d %d\n", value(), indexof());
    return cell != 6 || pair.left != 4 || pair.right != 2;
}
