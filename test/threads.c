#include <errno.h>
#include <pthread.h>
#undef pthread_equal

static unsigned char marker = 81;

static char *first_literal;
static _Thread_local int counter = 7;

static char *message(void) {
    return "Q";
}

static void *identify(void *value) {
    pthread_t self = pthread_self();
    if (counter != 7)
        return 0;
    counter = 9;
    if (!pthread_equal(self, self))
        return 0;
    char *text = message();
    if (value) {
        first_literal = text;
        return value;
    }
    return text;
}

int main(int argc, char **argv) {
    pthread_t first;
    pthread_t second;
    void *received;
    void *second_literal;
    if (counter != 7)
        return 7;
    counter = 11;
    if (pthread_create(&first, 0, identify, &marker))
        return 1;
    if (pthread_create(&second, 0, identify, 0))
        return 2;
    if (pthread_equal(first, second))
        return 3;
    if (pthread_join(second, &second_literal) || pthread_join(first, &received))
        return 4;
    char *text = message();
    if (counter != 11)
        return 8;
    if (first_literal != text || second_literal != (void *)text)
        return 6;
    if (argc > 1) {
        pthread_t self = pthread_self();
        if (pthread_join(self, 0) != EDEADLK || pthread_join(first, 0) != ESRCH)
            return 5;
    }
    return *(unsigned char *)received;
}
