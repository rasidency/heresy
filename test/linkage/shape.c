static int bound_calls = 0;

int bound(void) {
    ++bound_calls;
    return 3;
}

int adjusted(int columns, int rows, int data[rows++][columns]) {
    columns = 8;
    return data[1][1] + (int)sizeof(data[0]) + rows;
}

int explicit_pointer(int columns, int (*data)[columns]) {
    columns = 9;
    data += 1;
    return (*data)[2] + (int)sizeof(*data);
}

int effectful(int (*data)[bound()]) {
    return data[1][1] + (int)sizeof(*data) + bound_calls;
}

void fill(int columns, int early, int (*data)[columns]) {
    data[1][1] = 7;
    if (early)
        return;
    data[1][2] = 8;
}
