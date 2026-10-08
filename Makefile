.PHONY: test check paper
SBCL_TEST_HEAP_MB ?= 2048
test:
	sbcl --dynamic-space-size $(SBCL_TEST_HEAP_MB) --no-sysinit --no-userinit --script scripts/test.lisp
check: test
	git diff --check
paper:
	$(MAKE) -C paper
