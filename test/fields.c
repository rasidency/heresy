#include <complex.h>
#include <stdio.h>

struct Fields {
    unsigned int first : 5;
    signed int signed_value : 8;
    unsigned int tail : 7;
    unsigned char marker;
};

typedef struct {
    union { int words[4]; unsigned char bytes[16]; } payload;
} Cursor;

static struct Fields packed = {3, 4, 5, 68};

struct __attribute__((packed)) Packet {
    unsigned char tag;
    unsigned int mode : 3;
    signed int delta : 6;
    unsigned int : 0;
    unsigned long counter;
};

int main(void) {
    int plain = ((struct { char first; int second; }){1, 8}).second;
    unsigned bits = ((struct { unsigned : 1; unsigned : 0; unsigned field : 3; }){.field = 5}).field;
    int nested = ((struct { struct { int number; }; }){.number = 22}).number;
    Cursor cursor = {.payload.words = {17}};
    if ((int)cimag(CMPLX(4.0, 2.75)) != 2)
        return 3;
    if (plain != 8 || bits != 5 || nested != 22 || cursor.payload.words[0] != 17)
        return 2;
    struct Packet packet = {9, 5, -4, 19};
    if (sizeof(packet) != 12 || _Alignof(struct Packet) != 1 ||
        packet.tag != 9 || packet.mode != 5 || packet.delta != -4 || packet.counter != 19)
        return 1;
    packed.signed_value = 0 - 3;
    putchar(packed.signed_value + 68);
    putchar(packed.first + 63);
    putchar(packed.tail + 62);
    putchar(packed.marker);
    putchar('\n');
    return packed.first - 3;
}
