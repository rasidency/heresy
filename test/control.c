#include <stdio.h>

static int choose(int code) {
    if (code == 0) {
        int answer = 65;
        return answer;
    } else {
        int answer = 88;
        return answer;
    }
}

static int scan(int limit) {
    for (int i = 0; i < limit; i = i + 1) {
        if (i == 1)
            continue;
        int j = 0;
        do {
            j = j + 1;
            if (j == 1)
                continue;
            if (i == 3)
                return 68;
            if (i == 2)
                break;
            putchar(66);
        } while (j < 2);
        if (i == 2)
            putchar(67);
    }
    return 89;
}

int main(void) {
    int first = choose(0);
    putchar(first);
    int last = scan(4);
    putchar(last);
    do {
        putchar(69);
        continue;
    } while (0);
    for (;;)
        break;
    putchar(10);
    return 7;
}
