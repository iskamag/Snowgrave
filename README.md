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

The [paper](paper/README.md) describes the design and current implementation scope.
