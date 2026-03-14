#!/bin/bash
# Quick development test script for chibicc tests
# Usage: ./test.sh [test_name...]
# Examples:
#   ./test.sh              # run all chibicc tests
#   ./test.sh string enum  # run specific tests
#   ./test.sh --inline     # run inline tests only

set -e
CIVET=".build/debug/Civet"
TMP=$(mktemp -d)
trap "rm -rf $TMP" EXIT

if [ "$1" = "--inline" ]; then
    exec bash Tests/run.sh
fi

TESTS="${@:-alignof alloca arith asm attribute bitfield builtin cast commonsym complit compat const constexpr control decl enum extern float generic initializer literal macro offsetof pointer sizeof stdhdr string struct typedef typeof unicode union usualconv varargs variable vla}"

swift build -q 2>&1

for test in $TESTS; do
    printf "%-15s" "$test:"
    if ! $CIVET "Tests/CivetTests/Fixtures/chibicc/${test}.c" > "$TMP/${test}.s" 2>"$TMP/${test}.err"; then
        echo "FAIL(compile)"
        cat "$TMP/${test}.err" | head -3
        continue
    fi
    if ! gcc -o "$TMP/${test}" "$TMP/${test}.s" -xc Tests/CivetTests/Fixtures/chibicc/common 2>"$TMP/${test}.link.err"; then
        echo "FAIL(asm/link)"
        cat "$TMP/${test}.link.err" | head -3
        continue
    fi
    if "$TMP/${test}" > "$TMP/${test}.out" 2>&1; then
        echo "PASS"
    else
        code=$?
        if [ $code -eq 139 ]; then
            echo "FAIL(segfault)"
        elif [ $code -eq 1 ]; then
            echo "FAIL(wrong answer)"
            tail -1 "$TMP/${test}.out"
        else
            echo "FAIL(exit=$code)"
        fi
    fi
done
