#include <stdio.h>

static int evaluate(int early) {
    int effects = 0;
    int result = _Generic(++effects, int: ({
        int sum = 0;
        for (int i = 0; i < 6; ++i) {
            int value = ({
                if (i == 1) continue;
                if (i == 4) break;
                if (early && i == 2) return 41;
                i + 3;
            });
            sum += value;
        }
        sum;
    }), default: 0);
    int labelled = ({
        int word = 2;
        goto finish;
        word = 30;
        finish: word + 1;
    });
    return result + labelled + effects;
}

int main(void) {
    printf("%d %d\n", evaluate(0), evaluate(1));
    return 0;
}
