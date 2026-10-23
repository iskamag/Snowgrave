# Snowgrave

Snowgrave is an SBCL prototype that obtains effective methods through the MOP,
turns classes into structures, and recompiles the source so methods, helpers
and accessors use the generated ordinary functions.

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
It currently fails at dynamic class construction, before closed collection
runs. The complete index-set component passes closed execution and fresh
source/FASL replay.

The [paper](paper/README.md) describes the design and current implementation scope.
