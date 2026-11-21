#include <limits.h>
#include <pthread.h>
#include <stdatomic.h>
#include <stdio.h>

struct pair { int *first; long tag; };
struct triple { int *first; long tag, tail; };
static _Atomic int counter;

static void *increment(void *argument) {
    for (int i = 0; i < 8; ++i)
        atomic_fetch_add_explicit(&counter, 1, memory_order_relaxed);
    return argument;
}

int main(void) {
    int cells[2] = {4, 9};
    _Atomic(int *) current;
    atomic_store(&current, cells);
    unsigned char *raw = (unsigned char *)&current;
    raw[0] ^= 1;
    int *snapshot = atomic_load(&current);
    raw[0] ^= 1;
    int *wanted = cells + 1;
    int miss = atomic_compare_exchange_strong(&current, &wanted, cells + 1);
    int hit = atomic_compare_exchange_strong(&current, &wanted, cells + 1);
    int *replaced = atomic_exchange(&current, cells);
    atomic_fetch_add(&current, 1);
    if (snapshot != cells || miss || !hit || wanted != cells || *replaced != 9 || atomic_load(&current) != cells)
        return 4;
    _Atomic(struct pair) pair = (struct pair){cells, 7};
    struct pair old = atomic_exchange(&pair, ((struct pair){cells + 1, 9}));
    struct triple wide = {cells, 1, 2}, replacement = {cells + 1, 3, 4}, previous;
    __atomic_exchange(&wide, &replacement, &previous, __ATOMIC_SEQ_CST);
    int equal = __atomic_compare_exchange(&wide, &previous, &replacement, 0, __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST);
    if (old.tag != 7 || equal || *previous.first != 9 || previous.tail != 4)
        return 5;
    atomic_init(&counter, INT_MAX);
    int before = atomic_fetch_add(&counter, 1);
    int wrapped = atomic_exchange(&counter, 7);
    int bits = atomic_fetch_xor(&counter, 3);
    int mask = atomic_fetch_and(&counter, 6);
    int low = atomic_fetch_or(&counter, 1);
    int high = atomic_fetch_sub(&counter, 2);
    int after = atomic_load(&counter);
    int expected = 19;
    int missed = atomic_compare_exchange_weak_explicit(&counter, &expected, 11,
        memory_order_acq_rel, memory_order_acquire);
    int observed = expected;
    int changed = atomic_compare_exchange_strong(&counter, &expected, 23);
    if (missed || observed != 3 || !changed || expected != 3 || atomic_load(&counter) != 23)
        return 3;
    atomic_store(&counter, 0);
    pthread_t first, second;
    if (pthread_create(&first, 0, increment, 0) || pthread_create(&second, 0, increment, 0))
        return 1;
    if (pthread_join(first, 0) || pthread_join(second, 0))
        return 2;
    printf("%d %d %d %d %d %d %d %d\n", before, wrapped, bits, mask, low, high, after, atomic_load(&counter));
    return 0;
}
