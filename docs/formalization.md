# Lean formalization

The repository distinguishes independent publication from formal dependency.
Every PDF remains independently assembled from its owning directory. Lean
modules may depend on the pinned Mathlib revision and on the deliberately thin
`Textbooks.Foundation` layer.

## Trust and dependency model

The checked proof chain is:

```text
Lean kernel
  -> pinned Lean and Mathlib versions
  -> Textbooks.Foundation
  -> one textbook namespace
```

`Textbooks.Foundation` contains shared notation, Mathlib interoperability
lemmas, and results genuinely used by more than one textbook. It must not become
a second, repository-local replacement for Mathlib.

Book modules may import Mathlib, Foundation, and modules owned by the same book.
Direct imports from another textbook are rejected. Prefer Mathlib first; promote
a genuinely shared adapter to Foundation when necessary. An exceptional
cross-book dependency requires an architecture-policy change and a deliberately
small public API.

## Foundation promotion policy

Foundation is demand-driven. Decide where a declaration belongs in this order:

1. Use an existing Mathlib declaration when it states the required result.
2. Keep a new declaration in the first book namespace that needs it.
3. When a second, independent book namespace needs the same declaration or the
   same nontrivial Mathlib adapter, consider promoting it to Foundation.

Promotion is appropriate only when the declaration has a book-neutral statement,
has at least two concrete book consumers, and can form part of a small, stable
shared API. Repository-wide notation and conventions, or an interoperability
lemma required to make those conventions work with Mathlib, may be promoted
before a second consumer exists when their repository-wide scope is clear.

Do not promote a declaration merely because it is elementary, foundational in
the pedagogical sense, or likely to be reused later. In particular, keep the
following out of Foundation:

- a result already provided adequately by Mathlib;
- a theorem whose statement depends on one book's exposition, notation, or
  chapter sequence;
- a convenience lemma with only one concrete book consumer; and
- a re-export or thin alias whose only purpose is to hide a Mathlib name.

Different books may prove their printed formulations with separate thin wrapper
theorems over the same Mathlib result. Those wrappers remain in their owning book
namespaces and provide stable declarations for the proof-index shards; their shared
Mathlib dependency does not by itself justify Foundation code.

When promoting an existing declaration, move only the smallest book-neutral
definition or lemma needed by the consumers. Update both book modules to import
that Foundation module directly, and validate all affected books. Cross-book
expository references may still identify where a result is taught, but they do
not create a Lean import dependency between book namespaces.

## Source layout

```text
lean/
  lean-toolchain
  lakefile.toml
  lake-manifest.json
  Textbooks.lean
  Textbooks/
    Foundation.lean
    ElementaryNumberTheory/
    LinearAlgebra/
    MathematicalAnalysis/
```

Use chapter directories inside the owning Lean namespace as formalization grows.
Lean files need not match LaTeX section files one-to-one. Stable linkage happens
at the labeled theorem level, so declaration names should describe mathematics
rather than printed theorem numbers.

Set `autoImplicit false` in repository modules. Do not use `sorry`, `admit`,
or new unchecked `axiom` declarations in checked sources.

## Linking a verified proof
A verified LaTeX theorem needs all three parts:


1. A repository-global theorem label such as `an:thm:compactness`.
2. A `\leanverified{an:thm:compactness}` marker adjacent to the theorem.
3. An entry in the matching `proof-index/<book>/<chapter>.yml` shard naming
   its Lean declaration.

Each shard is owned by one registered book and one chapter:

```yaml
book: mathematical-analysis
chapter: 02-basic-topology

proofs:
  - id: an:thm:compactness
    tex: chapters/02-basic-topology/03-compact-sets.tex
    declaration: Textbooks.MathematicalAnalysis.Chapter02.compactness
    foundations:
      - topology
```

The shard path, `book`, `chapter`, and each entry's `tex` chapter must
agree. The checker loads shards in sorted order and enforces theorem-label and
Lean-declaration uniqueness across the complete repository.

The `foundations` list is editorial metadata, not a duplicate dependency
graph. Lean imports remain the mechanical source of dependency truth.
`scripts/check-proof-links.py` confirms that the book is registered, the
source path is safe, the label and marker occur in that file, identifiers are
unique, every marker is registered, and each label prefix and declaration

namespace belongs to the named book. It also rejects cross-book imports and
Lean source files outside the `Textbooks` import closure, and confirms that each
registered declaration exists after `import Textbooks`. Temporary declaration
probes belong under
`build/lean-links/`.

A marker means only that the associated formal statement has a kernel-checked
proof. Human review must still confirm that the Lean statement faithfully
represents the natural-language theorem and its intended hypotheses.

## Commands

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

Dependency updates are intentional maintenance tasks. Change
`lean/lean-toolchain` and the Mathlib revision together, run `lake update`
inside `lean/`, review the resulting `lake-manifest.json`, and commit all
three files. Ordinary checks must not run `lake update`.

## Scope and coverage

Do not claim that an entire textbook is formally verified merely because the
Lean project builds. Coverage is the set of entries loaded from the chapter
shards under `proof-index/`.
Material omitted pedagogically, such as set-theoretic foundations in an analysis
text, may be supplied by Mathlib or Foundation and should be described as a
prerequisite at chapter or book level.
