#include <stdio.h>

static int route(int selector) {
    int repeats = 0;
    goto enter;
again:
    repeats = repeats + 1;
enter:
    switch (selector) {
        case 1:
            putchar(65);
        case 2:
            putchar(66);
            break;
        case 3 ... 5:
            putchar(67);
            goto done;
        default:
            putchar(68);
    }
    if (repeats == 0) {
        putchar(69);
        goto again;
    } else {
        putchar(70);
        goto done;
    }
done:
    return repeats;
}

static int indirect(int first) {
    goto *(first ? &&left : &&right);
left:
    return 72;
right:
    return 73;
}

static int indexed(int index) {
    static void *const targets[] = {&&left, &&right};
    goto *targets[index];
left:
    return 72;
right:
    return 73;
}

int main(void) {
    int first = route(1);
    int ranged = route(4);
    int fallback = route(7);
    for (int i = 0; i < 2; i = i + 1) {
        switch (i) {
            case 0:
                continue;
        }
        putchar(71);
    }
    int left = indirect(1);
    int right = indirect(0);
    if (left != indexed(0) || right != indexed(1))
        return 3;
    putchar(left);
    putchar(right);
    putchar(10);
    return first + ranged + fallback;
}
