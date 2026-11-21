#include "packet.h"

struct Packet change(struct Packet value, int *counter) {
    ++value.code;
    value.kind += 256;
    *counter += 2;
    return value;
}

struct Packet redirect(struct Packet value, int *pointer) {
    value.pointer = pointer;
    return value;
}

union Choice choose(union Choice value, int *pointer) {
    value.pointer = pointer;
    return value;
}
