# Lean formalization

The repository distinguishes independent publication from formal dependency.
Every PDF remains independently assembled from its owning directory. Lean
modules depend directly on the pinned Mathlib revision and remain within their
own textbook namespace.

## Trust and dependency model

The checked proof chain is:

```text
Lean kernel
  -> pinned Lean and Mathlib versions
  -> one textbook namespace
```

## Dependency policy

Book modules may import Mathlib and modules owned by the same book. Direct
imports from another textbook are rejected. When another textbook has already
formalized a needed mathematical result, use the corresponding Mathlib
declaration instead of importing that textbook. If Mathlib does not yet contain
the reusable result, contribute the general result upstream when practical or keep
separate book-local proofs; do not introduce a cross-book dependency.

Each book may keep a thin wrapper theorem when its printed formulation, notation,
or theorem name differs from Mathlib. Those wrappers remain in the owning book
namespace and provide stable declarations for proof-index entries. Do not create
a repository-local shared foundation or re-export layer merely to hide Mathlib
names.

## Source layout

```text
lean/
  lean-toolchain
  lakefile.toml
  lake-manifest.json
  Textbooks.lean
  Textbooks/
    ElementaryNumberTheory/
    LinearAlgebra/
    MathematicalAnalysis1/
    MathematicalAnalysis2/
```

Use chapter directories inside the owning Lean namespace as formalization grows.
Lean files need not match LaTeX section files one-to-one. Stable linkage happens
at the labeled theorem level, so declaration names should describe mathematics
rather than printed theorem numbers.

Set `autoImplicit false` in repository modules. Do not use `sorry`, `admit`,
or new unchecked `axiom` declarations in checked sources.

## Linking a verified proof
A verified LaTeX theorem needs two parts:

1. A repository-global theorem label such as `an1:thm:compactness`.
2. An entry in the matching `proof-index/<book>/<chapter>.yml` shard naming
   its Lean declaration.

Each shard is owned by one registered book and one chapter:

```yaml
proofs:
  - id: an1:thm:compactness
    declaration: Textbooks.MathematicalAnalysis1.Chapter02.compactness
```

The shard path is the source of its book and chapter. The checker resolves each
repository-global theorem label to its LaTeX source file and requires that file
to belong to the shard's chapter, so entries do not repeat `book`, `chapter`, or
`tex` paths. It loads shards in sorted order and enforces theorem-label and
Lean-declaration uniqueness across the complete repository.

`scripts/check-proof-links.py` confirms that the book is registered, the
label resolves uniquely, identifiers are unique,
and each label prefix and declaration namespace belongs to the named book. It
also rejects cross-book imports and
Lean source files outside the `Textbooks` import closure, and confirms that each
registered declaration exists after `import Textbooks`. Temporary declaration
probes belong under
`build/lean-links/`.

An index entry means only that the associated formal statement has a kernel-checked
proof. Human review must still confirm that the Lean statement faithfully
represents the natural-language theorem and its intended hypotheses.

## Validation commands

```sh
make check proof-links
make lean
make lean check
make check all strict
```

`make check proof-links` is fast and does not invoke Lean. `make lean check`
builds the pinned Lake project, rejects proof escape hatches, and validates every
registered declaration. `make check all strict` makes this a required gate before the
LaTeX builds.

## Dependency updates

Dependency updates are intentional maintenance tasks. Change
`lean/lean-toolchain` and the Mathlib revision together, run `lake update`
inside `lean/`, review the resulting `lake-manifest.json`, and commit all
three files. Ordinary checks must not run `lake update`.

## Scope and coverage

Do not claim that an entire textbook is formally verified merely because the
Lean project builds. Coverage is the set of entries loaded from the chapter
shards under `proof-index/`.
Material omitted pedagogically may be supplied by Mathlib and should be described
as a prerequisite at chapter or book level.
