.PHONY: test check paper check-clamsara check-clamsara-index-set check-clamsara-configuration
LISP ?= sbcl
SBCL_TEST_HEAP_MB ?= 1024
CLAMSARA_ROOT ?= ../Clamsara/.worktrees/sane-engine
# Set empty when the dependencies are already registered with ASDF.
QUICKLISP_SETUP ?= $(wildcard $(HOME)/quicklisp/setup.lisp)
ifeq ($(notdir $(LISP)),sbcl)
LISP_FLAGS = --dynamic-space-size $(SBCL_TEST_HEAP_MB) --noinform --no-sysinit --no-userinit --disable-debugger $(if $(QUICKLISP_SETUP),--load $(QUICKLISP_SETUP)) --script
else ifeq ($(notdir $(LISP)),ccl)
LISP_FLAGS = --no-init --batch $(if $(QUICKLISP_SETUP),--load $(QUICKLISP_SETUP)) --load
else ifeq ($(notdir $(LISP)),ecl)
LISP_FLAGS = -norc $(if $(QUICKLISP_SETUP),-load $(QUICKLISP_SETUP)) -shell
else
$(error Set LISP_FLAGS for the requested Lisp implementation)
endif
export SNOWGRAVE_CLAMSARA_ROOT := $(abspath $(CLAMSARA_ROOT))
test:
	$(LISP) $(LISP_FLAGS) scripts/test.lisp
check: test
	git diff --check
check-clamsara:
	$(LISP) $(LISP_FLAGS) scripts/check-clamsara.lisp
check-clamsara-index-set:
	$(LISP) $(LISP_FLAGS) scripts/check-clamsara-index-set.lisp
check-clamsara-configuration:
	$(LISP) $(LISP_FLAGS) scripts/check-clamsara-configuration.lisp
paper:
	$(MAKE) -C paper
