// Test instruction selection optimization patterns

int mul3(int x) { return x * 3; }          // expect: lea (%rdi,%rdi,2)
int mul5(int x) { return x * 5; }          // expect: lea (%rdi,%rdi,4)
int mul9(int x) { return x * 9; }          // expect: lea (%rdi,%rdi,8)
int mul8(int x) { return x * 8; }          // expect: shl $3
int mul0(int x) { return x * 0; }          // expect: xor
int mul1(int x) { return x * 1; }          // expect: mov only

unsigned udiv4(unsigned x) { return x / 4; }    // expect: shr $2
unsigned umod8(unsigned x) { return x % 8; }    // expect: and $7

int div1(int x) { return x / 1; }          // expect: mov only
int sdiv4(int x) { return x / 4; }         // expect: sar adjustment + sar

// Compound pattern: add + mul → lea
int add_mul4(int a, int b) { return a + b * 4; }  // expect: lea (%rdi,%rsi,4)

int main() {
    return mul3(7) + mul8(2) + udiv4(100) + umod8(15);
}
