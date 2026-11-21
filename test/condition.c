#include <pthread.h>

struct shared {
    pthread_mutex_t mutex;
    pthread_cond_t condition;
    int ready;
};

static void *publish(void *argument) {
    struct shared *state = argument;
    pthread_mutex_lock(&state->mutex);
    state->ready = 1;
    pthread_cond_signal(&state->condition);
    pthread_mutex_unlock(&state->mutex);
    return argument;
}

int main(void) {
    struct shared state = {PTHREAD_MUTEX_INITIALIZER, PTHREAD_COND_INITIALIZER, 0};
    pthread_t worker;
    if (pthread_mutex_lock(&state.mutex) || pthread_mutex_trylock(&state.mutex) != 16)
        return 2;
    if (pthread_create(&worker, 0, publish, &state))
        return 3;
    while (!state.ready)
        if (pthread_cond_wait(&state.condition, &state.mutex))
            return 4;
    if (pthread_mutex_unlock(&state.mutex) || pthread_join(worker, 0))
        return 5;
    if (pthread_cond_destroy(&state.condition) || pthread_mutex_destroy(&state.mutex))
        return 6;
    if (pthread_mutex_init(&state.mutex, 0) || pthread_cond_init(&state.condition, 0))
        return 1;
    return pthread_cond_destroy(&state.condition) || pthread_mutex_destroy(&state.mutex);
}
