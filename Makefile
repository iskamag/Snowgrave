.PHONY: test check paper check-clamsara check-clamsara-index-set
SBCL_TEST_HEAP_MB ?= 1024
CLAMSARA_ROOT ?= ../Clamsara/.worktrees/sane-engine
test:
	sbcl --dynamic-space-size $(SBCL_TEST_HEAP_MB) --no-sysinit --no-userinit --script scripts/test.lisp
check: test
	git diff --check
check-clamsara:
	sbcl --dynamic-space-size $(SBCL_TEST_HEAP_MB) --no-sysinit --no-userinit --script scripts/check-clamsara.lisp "$(CLAMSARA_ROOT)"
check-clamsara-index-set:
	sbcl --dynamic-space-size $(SBCL_TEST_HEAP_MB) --no-sysinit --no-userinit --script scripts/check-clamsara-index-set.lisp "$(CLAMSARA_ROOT)"
paper:
	$(MAKE) -C paper
