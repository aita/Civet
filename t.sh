#!/bin/bash
# Quick single-file test: ./t.sh <file.c>
# Or chibicc test: ./t.sh string (looks in Vendor/chibicc/test/)
set -e
CIVET=".build/debug/Civet"
OUT="/tmp/civet_test"

FILE="$1"
if [ -z "$FILE" ]; then echo "Usage: ./t.sh <file.c|testname>"; exit 1; fi
if [ ! -f "$FILE" ]; then
    FILE="Vendor/chibicc/test/${1}.c"
fi
if [ ! -f "$FILE" ]; then echo "Not found: $1"; exit 1; fi

$CIVET "$FILE" > "${OUT}.s" 2>/dev/null
gcc -o "$OUT" "${OUT}.s" -xc Vendor/chibicc/test/common 2>/dev/null
"$OUT"; echo "exit: $?"
