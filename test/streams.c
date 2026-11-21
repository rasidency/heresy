#include <stdio.h>

int main(int argc, char **argv) {
    if (argc < 2 || argc > 3)
        return 1;
    FILE *file = fopen(argv[1], "rb");
    if (!file)
        return 2;
    unsigned char bytes[6] = {0};
    unsigned long used = fread(bytes, 2, 3, file);
    unsigned long empty = fread(0, 0, 3, file);
    int status = fclose(file);
    if (argc == 3) {
        file = fopen(argv[2], "wb");
        if (!file)
            return 3;
        unsigned long written = fwrite(bytes, 1, 4, file);
        int closed = fclose(file);
        if (written != 4 || closed)
            return 4;
    }
    printf("%lu %lu %u %u %u %u %d\n", used, empty, bytes[0], bytes[1], bytes[2], bytes[3], status);
    return 0;
}
