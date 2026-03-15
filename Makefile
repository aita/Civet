.PHONY: build test test-chibicc test-swift clean

build:
	swift build

test: test-chibicc test-swift

test-chibicc:
	python3 tools/civet-test chibicc

test-swift:
	swift test

clean:
	swift package clean
