#include <stdio.h>

struct Packet {
    unsigned char marker;
    int number;
    unsigned long stamp;
    unsigned char *tail;
};

struct Tail {
    int number;
    unsigned char marker;
};

union Word {
    int integer;
    unsigned char character;
};

static unsigned char end = 68;
static struct Packet packet = {65, 66, (unsigned long)67, &end};
static struct Packet *chosen = &packet;
static struct Tail padded = {0, 69};
static union Word word = {.character = 70};

int main(void) {
    struct Packet copy = {chosen->marker, chosen->number, chosen->stamp, chosen->tail};
    struct Packet saved = copy;
    copy.tail = &padded.marker;
    copy = saved;
    putchar(copy.marker);
    putchar(copy.number);
    putchar((int)copy.stamp);
    unsigned char *tail = copy.tail;
    putchar(*tail);
    putchar(padded.marker);
    putchar(word.integer);
    putchar(10);
    copy.number = padded.number;
    return copy.number;
}
