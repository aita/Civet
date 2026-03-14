// Optimization demo: exercises LVN, constant folding, DCE, branch simplification

int constant_fold() {
    int a = 2 + 3;       // fold → 5
    int b = a * 4;       // LVN propagates a=5, fold → 20
    return b;            // LVN propagates b=20
}

int dead_code() {
    int x = 10;
    int y = 20;          // unused → DCE removes
    int z = x + 1;
    return z;
}

int branch_simplify(int x) {
    if (1)               // constant test → branch simplified to goto
        return x;
    return 0;            // dead block eliminated
}

int cse(int a, int b) {
    int x = a + b;
    int y = a + b;       // CSE → y = x
    return x + y;
}
