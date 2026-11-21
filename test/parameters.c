#include <stdio.h>

int bound(void);
int adjusted(int columns, int rows, int data[rows++][columns]);
int explicit_pointer(int columns, int (*data)[columns]);
int effectful(int (*data)[bound()]);
void fill(int columns, int early, int (*data)[columns]);

int main(void) {
    int rows = 2;
    int columns = 3;
    int values[rows][columns];
    fill(columns, 1, values);
    if (values[1][1] != 7)
        return 2;
    fill(columns, 0, values);
    int adjusted_size = adjusted(columns, rows, values);
    int pointer_size = explicit_pointer(columns, values);
    int captured_size = effectful(values);
    if (adjusted_size != 22 || pointer_size != 20 || captured_size != 20)
        return 1;
    putchar('P');
    putchar('\n');
    return 0;
}
