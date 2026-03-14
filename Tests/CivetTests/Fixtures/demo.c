int fib(int n) {
    if (n <= 1)
        return n;
    return fib(n - 1) + fib(n - 2);
}

int abs(int x) {
    if (x < 0)
        return -x;
    return x;
}

int main() {
    int n = 10;
    int result = fib(n);
    int value = -5;
    int abs_value = abs(value);
    return abs_value + result;
}