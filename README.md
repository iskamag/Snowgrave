# Snowgrave

Snowgrave obtains effective-method source through Closer MOP, turns classes
into structures, and recompiles ordinary Lisp source. `bind-entry` specializes
an entry for a fixed component graph, seals its component roles, and rejects
unresolved method or slot selection. Its generic path uses portable source
transformations, with small host adapters for macro-expansion normalization.

Install `closer-mop` and `cl-form-types` through Quicklisp or register them with
ASDF, then load from the repository root:

```lisp
(require :asdf)
(asdf:load-asd (truename "snowgrave.asd"))
(asdf:load-system "snowgrave")
```

Run `make check`, `make check LISP=ccl`, or `make check LISP=ecl`.
The Makefile loads `~/quicklisp/setup.lisp` when present; override
`QUICKLISP_SETUP` as needed. `SBCL_TEST_HEAP_MB` defaults to 1024.

The optional Clamsara gates are `make check-clamsara`,
`make check-clamsara-index-set`, and `make check-clamsara-configuration`.
Set `CLAMSARA_ROOT` to the engine rewrite checkout and ensure its dependencies
are registered with ASDF. The gates compare original and closed execution,
poison original functions, and replay emitted source and compiled files in
fresh processes. For cross-host replay of the whole-engine artifact, set
`SNOWGRAVE_REPLAY_LISP=ccl` while closing on SBCL (or the reverse).
The configuration gate tests four simultaneous collectors
with the general closed selectors poisoned as well.

Configured bindings are live host functions. Independent configured-image
export and native Mezzano admission still require target work. The
[paper](paper/README.md) specifies the supported source fragment and boundaries.
