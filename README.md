# Snowgrave

Snowgrave is an SBCL prototype that obtains effective methods through the MOP,
turns classes into structures, and recompiles the source so methods, helpers
and accessors use the generated ordinary functions.
`bind-entry` specializes an entry for a configured component graph. It seals
declared component roles and rejects unresolved method or slot selection.

From the repository root:

```lisp
(require :asdf)
(asdf:load-asd (truename "snowgrave.asd"))
(asdf:load-system "snowgrave")
```

Run the tests with `make check`.

Run the optional Clamsara gates with `make check-clamsara` or
`make check-clamsara-index-set`, setting `CLAMSARA_ROOT` to its engine rewrite
checkout. The whole-engine gate also needs Closer MOP registered with ASDF.
The gates compare original and closed execution, disable the original
functions, and replay generated source and FASLs in fresh SBCL processes.
The whole-engine gate closes all engine and word-memory definitions and runs
selected unchanged collector workloads. The other gate exercises the complete
index-set component. Set `SBCL_TEST_HEAP_MB` to change the compiler heap
(default: 1024 MiB).

`make check-clamsara-configuration` tests four simultaneous configured
collectors, poisons the original and general closed generics, and measures
collection time and allocation. It also demonstrates `bind-entry` and role
exchange declarations. Configured bindings currently return live SBCL
functions; independent configured-image replay and native Mezzano admission
are not implemented.

The [paper](paper/README.md) describes the design and current implementation scope.
