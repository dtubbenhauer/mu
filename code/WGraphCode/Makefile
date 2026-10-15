.PHONY: all c rust test quick-test

all: c rust

c:
	$(MAKE) -C c

rust:
	cargo build --locked --profile release-lto

test: all
	$(MAKE) -C c test
	cargo test --locked
	python3 tests/check_workflows.py
	python3 tests/compare_implementations.py

quick-test: all
	$(MAKE) -C c test
	cargo test --locked
	python3 tests/compare_implementations.py --quick
