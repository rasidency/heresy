#include <stdio.h>

struct Fields {
    unsigned int first : 5;
    signed int signed_value : 8;
    unsigned int tail : 7;
    unsigned char marker;
};

static struct Fields packed = {3, 4, 5, 68};

int main(void) {
    packed.signed_value = 0 - 3;
    putchar(packed.signed_value + 68);
    putchar(packed.first + 63);
    putchar(packed.tail + 62);
    putchar(packed.marker);
    putchar('\n');
    return packed.first - 3;
}
