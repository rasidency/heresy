#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "linkage/packet.h"

int main(int argc, char **argv) {
    int *original = malloc(sizeof(int));
    int *alternate = malloc(sizeof(int));
    *original = 10;
    *alternate = 20;
    struct Packet seed = {original, 5, 'A'};
    struct Packet changed = change(seed, original);
    struct Packet redirected = seed;
    redirected = redirect(changed, alternate);
    union Choice choice = {.pointer = original};
    union Choice selected = choose(choice, alternate);
    unsigned char temporary = change(redirected, alternate).code;

    if (seed.kind != 5 || seed.code != 'A' || changed.kind != 261 || changed.code != 'B')
        return 1;
    if (*changed.pointer != 12 || *redirected.pointer != 22 || redirected.code != 'B' ||
        selected.pointer != alternate || *selected.pointer != 22 || choice.pointer != original || temporary != 'C')
        return 2;

    struct Packet duplicate;
    void *destination = memcpy(&duplicate, &changed, sizeof duplicate);
    if (destination != &duplicate || duplicate.pointer != original ||
        duplicate.kind != changed.kind || duplicate.code != changed.code)
        return 3;

    putchar(seed.code);
    putchar(changed.code);
    putchar(temporary);
    putchar('\n');
    free(original);
    if (argc > 1)
        return *duplicate.pointer;
    free(alternate);
    return 0;
}
