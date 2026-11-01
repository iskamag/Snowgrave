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

Use SBCL for routine checks. For portability checks, run
`ccl --no-init --batch --load ~/quicklisp/setup.lisp --load scripts/test.lisp`.
ECL is slower; use `ecl -norc -load ~/quicklisp/setup.lisp -shell scripts/test.lisp`
when checking its compatibility. Omit the setup load if ASDF already knows the
dependencies. Replace `scripts/test.lisp` with `examples/counter.lisp` to run
the example directly.

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
| `package.lisp`, `build.lisp`, `plans.lisp` | Public symbols, conditions, disposable build state, and explicit retained compiler contracts |
| `source.lisp`, `literals.lisp` | Definition indexing, open source, literal identity and cycles |
| `walker.lisp`, `normalize.lisp`, `hosts/` | Lexical traversal and portable macro-expansion snapshots |
| `admission.lisp`, `rewrite.lisp`, `functions.lisp` | Admission and name resolution, source rebuilding, entry domains, and ordinary definitions |
| `records.lisp`, `metadata.lisp`, `observation.lisp`, `usage.lisp` | Physical records, logical metadata, admitted comparisons, and the reachability scan that prunes them |
| `composition.lisp`, `methods.lisp`, `method-abi.lisp`, `dispatch.lisp` | MOP composition, continuations, argument transport, and finite method partitions |
| `artifact.lisp` | Residual source audit and independent source/metadata serialization |
| `configuration.lisp`, `configuration-entry.lisp` | Validate component graphs, compile bound implementations, and stage seal/code publication |
| `specialization/` | Conservative facts, lexical bindings, call selection, and form handlers |

Paths are relative to `src/`. MOP objects belong to the disposable build;
retained plans contain source, types, and layout descriptions. Runtime helpers
are emitted according to source reachability. Generated fields retain declared
types, and stores check them. Bound reads assert those types; unbound-slot
restarts can still supply values outside the slot declaration.

The rewriter uses one lexical traversal over frozen macro expansions.
Configured specialization tracks its own lexical facts. It expands stock
accessor leaves after slot selection and keeps authored helper graphs as
shared named calls; forcing every helper inline can duplicate those graphs
exponentially.

`tests/framework.lisp` provides differential fixtures, `tests/run.lisp` selects
the suites, and `support/host.lisp` supplies test process and allocation adapters.

## Supported fragment

The source cohort contains ordinary `defclass`, `defgeneric`, `defmethod`,
`defun`, `defvar`, `defparameter`, `defconstant`, and short-form
`define-method-combination` forms. Source packages must already exist.
Public entries have required parameters with declared domains.
Classes use standard metaclasses, instance slots, and stock initialization.

Method combinations may be standard or use an owned short-form definition.
Short combinations support primary ordering, around methods, single-method
identity, and function or macro operators. Owned combining helpers use closed
bindings, and their writes obey role seals. Macro operators receive the original
`call-method` syntax. Long-form combinations are rejected.
`call-next-method` accepts only the original argument list through direct
zero-argument calls. EQL specializers, custom initialization protocols, and
unresolved native-class intersections are rejected.

Records preserve logical class membership, slot boundness, checked stores,
and the admitted metadata queries. Physical CLOS/structure observations and
unsupported representation-sensitive operations are rejected. General closing
retains finite method selection. Closing executes source initialization in both
namespaces, so use trusted source with deliberate initialization effects.

## Configured entries

`bind-entry` returns a zero-argument function for fixed entry arguments. Its
`:roles` declarations seal component identities; an exchange group admits the
identities initially present in its slots. Ordinary data stays mutable and is
never sampled to justify method selection. All method and physical-slot choices
must resolve before compilation. Component construction, unresolved callbacks,
escaping owned callables, and authored load-time code are rejected.

Adding a seal updates ordinary writers and previously returned configured
functions. Affected implementations are compiled from their original argument
and role snapshots before publication. A failed compilation or publication
leaves existing bindings and seals intact. **Binding must not race execution
or another binding.** Generated writes use static identity guards.

Each unit lazily normalizes reached definitions once. Bindings with the same
entry, pairwise `eq` arguments, and equivalent role maps share compiled code.
Mutation dependencies identify known owners; unknown receivers conservatively
depend on the whole field. Replaced code is retired after its last binding is
updated.
Bindings and their retained recipes are host-local and have no independent
configured-image export.
