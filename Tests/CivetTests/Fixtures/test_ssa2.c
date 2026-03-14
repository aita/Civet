int test(int cond) {
    int x;
    if (cond) {
        x = 10;
    } else {
        x = 20;
    }
    return x;
}

int main() {
    return test(1) + test(0);
}
