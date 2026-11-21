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

enum Index { first_index = 0x100000000UL, next_index };
typedef enum Index Indices[2];

struct Wrapper {
    struct { int key; } head;
    union { unsigned int word; unsigned char byte; };
};

static unsigned char end = 68;
static struct Packet packet = {65, 66, (unsigned long)67, &end};
static struct Packet *chosen = &packet;
static struct Tail padded = {0, 69};
static union Word word = {.character = 70};

static int *left = (int[3]){5, 7};
static int *right = (int[3]){5, 7};
static const int *frozen = (const int[]){11};

static int advance(void) {
    static int tally = 3;
    return ++tally;
}

int main(void) {
    typedef struct Tail Outer;
    struct Tail { unsigned char marker; };
    struct Tail local = {12};
    Outer outer = {8, 3};
    struct Wrapper wrapper = {{17}, {.word = 66}};
    if (wrapper.head.key != 17 || wrapper.byte != 66)
        return 7;
    Outer rows[2] = {{1, 4}, {7, 9}};
    if (rows[1].number != 7 || rows[0].marker != 4)
        return 6;
    if (sizeof(local) != 1 || sizeof(outer) != 8 || local.marker + outer.marker != 15)
        return 5;
    static int tally = 9;
    if (advance() != 4 || advance() != 5 || tally != 9)
        return 4;
    left[1] = 13;
    if (right[1] != 7 || left[1] != 13 || left[2] || frozen[0] != 11)
        return 3;
    int matrix[2][3] = {{1, 2, 3}, {4, 5, 6}};
    if (matrix[1][2] != 6)
        return 1;
    enum { first = -3, second } index = second;
    Indices indices = {first_index, next_index};
    int selected = 0;
    int calls = 0;
    _Generic(++calls, int: selected, default: calls) = 7;
    if (selected != 7 || calls || index != -2 || indices[1] != 0x100000001UL)
        return 2;
    struct Packet copy = {chosen->marker, chosen->number, chosen->stamp, chosen->tail};
    struct Packet saved;
    saved = copy;
    copy.tail = &padded.marker;
    copy = saved;
    putchar(copy.marker);
    putchar(copy.number);
    putchar((int)copy.stamp);
    unsigned char *tail;
    unsigned char bytes[1];
    tail = copy.tail;
    bytes[0] = *tail;
    putchar(bytes[0]);
    putchar(padded.marker);
    putchar(word.integer);
    putchar(10);
    copy.number = padded.number;
    return copy.number;
}
