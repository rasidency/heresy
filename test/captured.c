#include <stdio.h>

static int visit(int depth) {
    int extent = depth + 1;
    int columns = 3;
    int values[extent++][2][columns];
    int last = extent - 2;
    columns = 9;
    values[last][1][2] = 'A' + depth;

    int saved = depth < 3 ? visit(depth + 1) : 0;
    int size = (int)sizeof(values);
    if (size != (extent - 1) * 24 || sizeof(values[0]) != 24 || sizeof(values[0][0]) != 12)
        return -1;
    if ((values + last) - values != last)
        return -2;
    putchar(values[last][1][2]);
    return saved + size;
}

int main(int argc, char **argv) {
    int *earlier = 0;
    int count = 2;
    for (int i = 0; i < 2; ++i) {
        int row[count][3];
        row[0][0] = 'A' + i;
        if (i == 0)
            earlier = &row[0][0];
        putchar(earlier[0]);
        ++count;
    }

    int result = visit(1);
    int length = 2;
    typedef int Grid[length++][3];
    length += 5;
    Grid grid;
    Grid other;
    grid[1][2] = 'E';
    other[1][2] = 'F';
    int width = 3;
    int (*cursor)[width] = grid;
    width = 9;
    ++cursor;
    if (sizeof(Grid) != 24 || sizeof(grid) != 24 || sizeof(other[0]) != 12 || length != 8 ||
        sizeof(*cursor) != 12 || (*cursor)[2] != 'E')
        return 8;
    putchar(grid[1][2]);
    putchar(other[1][2]);
    putchar('\n');
    if (argc > 1) {
        int bound = argc - 2;
        int invalid[bound];
        return (int)sizeof(invalid);
    }
    return result == 216 ? 0 : 7;
}
