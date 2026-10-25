# Development

The library depends on `closer-mop` and `cl-form-types` (which supplies the
`cl-environments` interface). Install their dependencies through Quicklisp or
an ASDF source registry. No sibling project is needed for the library, its
example, or its test suite.

From the repository root, load and test through ASDF:

```lisp
(require :asdf)
(asdf:load-asd (truename "snowgrave.asd"))
(asdf:load-system "snowgrave")
(asdf:test-system "snowgrave")
(load "examples/counter.lisp")
```

For a fresh SBCL process with Quicklisp dependencies:

```sh
sbcl --dynamic-space-size 1024 --no-sysinit --no-userinit --disable-debugger \
  --load ~/quicklisp/setup.lisp --script scripts/test.lisp
```

Use `ccl --no-init --batch --load ~/quicklisp/setup.lisp --load scripts/test.lisp`
or `ecl -norc -load ~/quicklisp/setup.lisp -shell scripts/test.lisp` for the
other hosts. Omit the setup load when the dependencies are registered with
ASDF another way. Replace `scripts/test.lisp` with `examples/counter.lisp` to
run the example directly.

The suite compares selected CLOS and closed executions, poisons original
bindings, and loads emitted source and compiled files in fresh processes.
SBCL and CCL also check warmed allocation counts; ECL runs those semantic
cases without an allocation counter. The example exercises construction,
ordinary entry calls, and configured binding.

## Source map

`close-source-unit` in `src/unit.lisp` coordinates the two compilation passes:

1. Read and own the source; index definitions and freeze macro expansions.
2. Compile disposable CLOS definitions in the open namespace.
3. Finalize layouts and obtain MOP method compositions; emit records and functions.
4. Rebind the complete source cohort, audit it, compile it, and discard the builder.

| Files | Responsibility |
| --- | --- |
| `package.lisp`, `build.lisp` | Public symbols, conditions, disposable build state, and owned names |
| `source.lisp`, `literals.lisp` | Definition indexing, open source, literal identity and cycles |
| `walker.lisp`, `normalize.lisp`, `hosts/` | Lexical traversal and portable macro-expansion snapshots |
| `rewrite.lisp`, `functions.lisp` | Closed bindings, entry domains, and ordinary definitions |
| `records.lisp`, `metadata.lisp`, `observation.lisp` | Physical records, logical metadata, and admitted comparisons |
| `composition.lisp`, `methods.lisp`, `method-abi.lisp`, `dispatch.lisp` | MOP composition, continuations, argument transport, and finite method partitions |
| `artifact.lisp` | Residual source audit and independent source/metadata serialization |
| `configuration.lisp`, `configuration-entry.lisp` | Validate component graphs, compile bound entries, and publish role seals |
| `specialization/` | Conservative facts, lexical bindings, call selection, and form handlers |

Paths in the table are relative to `src/`. A successful closed unit retains
ordinary source, functions, metadata, and specialization recipes. Open MOP
objects belong to the disposable build. Configured entries borrow live
closed values and seal only declared component roles; ordinary mutable fields
are never sampled to justify call selection. Their functions remain local to
the host process. Closing executes source initialization in both namespaces,
so use trusted source with deliberate initialization effects.

The test files follow the same responsibilities. `tests/framework.lisp`
provides differential fixtures, `tests/run.lisp` selects the suites, and
`support/host.lisp` contains process, GC, and allocation-counter adapters used
only by tests and integration tools.

## Optional Clamsara checks

These gates target Clamsara's engine rewrite, including its `engine/` sources
and `clamsara/word-memory` ASDF system. They are not part of the standalone
suite. Supply that checkout explicitly and register its dependencies:

```sh
export SNOWGRAVE_CLAMSARA_ROOT=/path/to/engine-rewrite
sbcl --dynamic-space-size 1024 --load ~/quicklisp/setup.lisp --script scripts/check-clamsara.lisp
sbcl --dynamic-space-size 1024 --load ~/quicklisp/setup.lisp --script scripts/check-clamsara-index-set.lisp
sbcl --dynamic-space-size 1024 --load ~/quicklisp/setup.lisp --script scripts/check-clamsara-configuration.lisp
```

The whole-engine gate compares original, closed, and poisoned-original runs,
then replays emitted source and compiled files in fresh processes. Set
`SNOWGRAVE_REPLAY_LISP=ccl` while closing on SBCL, or the reverse, to check
cross-host source transfer. Compiled files are specific to their host.
The configuration gate binds four collectors simultaneously and poisons the
general closed selectors. These workloads do not prove arbitrary collector
programs or native target admission.

## Supported fragment

The source cohort contains ordinary `defclass`, `defgeneric`, `defmethod`,
`defun`, `defvar`, `defparameter`, and `defconstant` forms. Source packages must
already exist. Public entries have required parameters with declared domains.
Classes use standard metaclasses, instance slots, and stock initialization.
Method combination is standard, and `call-next-method` accepts only the
original argument list through direct zero-argument calls. EQL specializers,
custom initialization protocols, and unresolved native-class intersections
are rejected.

Records preserve logical class membership, slot boundness, checked stores,
and the admitted metadata queries. Physical CLOS/structure observations and
unsupported representation-sensitive operations are rejected. General closing
retains finite method selection; configured binding additionally requires
resolving its method and physical-slot choices. Configured bindings reject
component construction, unresolved callbacks, escaping owned callables, and
authored load-time code. These are implementation boundaries, not a claim
that arbitrary Common Lisp programs can be closed.
