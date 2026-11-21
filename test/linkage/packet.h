struct Packet {
    int *pointer;
    unsigned short kind;
    unsigned char code;
};

union Choice {
    int *pointer;
    unsigned long raw;
};

struct Packet change(struct Packet value, int *counter);
struct Packet redirect(struct Packet value, int *pointer);
union Choice choose(union Choice value, int *pointer);
