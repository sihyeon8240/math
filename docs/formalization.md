# Lean formalization

The repository distinguishes independent publication from formal dependency.
Every PDF remains independently assembled from its owning directory. Lean
modules depend directly on the pinned Mathlib revision and remain within their
own textbook namespace.

## Authoring policy

For new or mathematically revised theorems selected for formalization, complete
the Lean statement and kernel-checked proof before writing or revising their
natural-language statement and proof. Lean is the reference for definitions,
hypotheses, conclusions, and the verified reasoning; LaTeX owns the educational
exposition and presentation.

Apply this workflow to new work and migrate existing textbook results gradually.
Existing unformalized material need not be converted as part of unrelated edits.
Motivation, historical notes, and illustrative examples do not require Lean
counterparts unless they are themselves selected for formalization. Typographical
and presentation-only changes do not require rewriting a Lean proof.

1. Write the needed definitions, theorem, and proof in the owning book's Lean
   namespace, include the module in the `Textbooks` import closure, and run
   `make lean check`. Use a book-local wrapper when the printed formulation
   differs from Mathlib.
2. Write the natural-language statement from the checked declaration. Preserve
   variable domains, quantifiers, hypotheses, and conclusions, including relevant
   implicit and typeclass assumptions. Explain prerequisite definitions. Pair
   the statement with its Lean declaration signature using the
   [paired exposition format](writing-guide.md#paired-mathematical-exposition-and-lean-code).
3. Write an educational proof grounded in the verified reasoning. Explain the
   mathematical steps and supporting lemmas rather than translating tactics
   line by line. Expand automated steps when readers need the explanation.
   Calling a Mathlib theorem alone does not supply a pedagogical proof: explain
   the required reasoning or identify the result as a cited prerequisite. Pair
   each mathematical reasoning unit with its corresponding Lean proof fragment.
4. Add the LaTeX label and matching chapter or appendix proof-index entry, then rerun
   `make lean check` and the affected textbook's build and log checks. Complete
   the repository validation required before review.
5. Review the correspondence in both directions: the prose must express the
   checked statement faithfully, and every substantive proof step must be
   justified within the verified assumptions. If the intended mathematics
   changes, update and check Lean before revising the prose.

CI checks proofs and registered links; it cannot establish authoring order or
the fidelity of a natural-language translation. Contributors and human reviewers
remain responsible for those requirements, including AI-assisted exposition.

### Displayed-code correspondence

The complete declaration and proof in the owning `.lean` module are the checked
formal source. Code displayed in LaTeX must reproduce the corresponding
signature and proof fragments from that source, allowing presentation-only
indentation changes. Imports, namespace context, and the declaration-to-proof
connector may remain outside the displayed fragments; make any context needed
to understand them clear. Do not substitute an unchecked alternative proof or
silently omit substantive reasoning from the displayed sequence.

Update displayed code together with changes to the corresponding Lean source.
Review the natural-language statement, each explanation/code pair, and the
complete checked declaration for agreement. A proof fragment can depend on
previous fragments and need not compile independently.

`make lean check` checks the Lean project and registered proof links; it does not
extract or compile code printed in LaTeX or establish that copied fragments
match the checked source. A successful PDF build only establishes that the
code can be typeset. Contributors and reviewers must check this correspondence
explicitly, including when only the displayed code changes.

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

## Book-owned prerequisite boundaries

This repository has no common mathematical prerequisite baseline. Each book owns
its starting assumptions in `books/<slug>/formalization.md`, including its choice
of logic and foundational principles. A future book on set theory, mathematical
logic, or model theory must specify its own boundary; it does not inherit the
starting assumptions of an analysis or algebra textbook. Repository proof-safety
requirements still apply: an accepted mathematical premise is implemented by an
existing checked result or an explicit hypothesis, not a new unchecked axiom.
Distinguish the logic being studied from the Lean metatheory used to formalize
it; the book policy does not change the repository's kernel trust boundary.

Start new book policies from the
[formalization boundary template](../common/templates/formalization.md), also
copied by `make new-book`. Complete its prompts before formalization; the template
does not authorize any mathematical prerequisites.

Current book policies are:

- [Elementary Number Theory](../books/elementary-number-theory/formalization.md).
- [Linear Algebra](../books/linear-algebra/formalization.md).
- [Mathematical Analysis I](../books/mathematical-analysis-1/formalization.md).
- [Mathematical Analysis II](../books/mathematical-analysis-2/formalization.md).

Each policy records starting structures, accepted results, results developed in
the book, and scoped external exceptions. Describe
mathematical boundaries precisely enough to decide whether a proof is allowed;
"basic algebra" or "results from other subjects" alone is insufficient. Before
using a substantive external result outside the recorded boundary, amend the
owning policy and review that amendment together with its first use. An exception
must identify the result, where it is allowed, and why it is needed. Acceptance
in one book does not authorize use in another.

## Proof roles and permitted dependencies

Classify formalized results in their module documentation or declaration
docstrings using the following roles; the proof-index schema remains unchanged.

| Role | Permitted proof dependencies |
|---|---|
| Prerequisite | Direct Mathlib citation within the owning book's accepted boundary; document its role as an assumed result. |
| Core result | Accepted prerequisites and earlier established results of the same book, with permitted bookkeeping lemmas. |
| Supporting lemma | Reuse Mathlib for logical, representational, and elementary computational steps within the book's boundary; classify substantive new mathematics as a prerequisite or core result. |

A core proof must not invoke the target's Mathlib counterpart, an equivalent
result, or an unaccepted stronger result that supplies the essential argument.
Judge a supporting lemma by the mathematics it supplies, not its name or length.
Alternative proofs using additional external theory must be labeled separately
and have their extra prerequisites recorded; they do not replace the core proof.

The intended bottom-up order is the book's mathematical dependency order, which
must be acyclic and consistent with its exposition. Reuse Mathlib's standard
structures and definitions rather than reconstructing their implementations.
This policy does not require every transitive implementation dependency inside
Mathlib to follow the textbook's chapter order.

Prefer focused imports, but imports alone do not establish compliance. Review
actual proof dependencies, including implicit typeclass assumptions and facts
used by simplification or search. Automation may discharge routine steps within
the accepted boundary; it must not conceal the core mathematical argument or
supply an unaccepted result. Use explicit lemmas or restricted automation such as
`simp only [...]` when needed to make the dependency boundary reviewable. No
particular tactic is universally authorized as mathematical background.

## Statements and citation policy

The checked Lean statement must faithfully match the textbook's domains,
quantifiers, hypotheses, and conclusion. Prefer Mathlib's standard definitions
and interfaces. When the intended statement has the same assumptions, conclusion,
and generality as an existing Mathlib theorem, prefer its statement shape;
identical syntax or proof implementation is not required. Do not generalize a
textbook theorem merely to match Mathlib, or silently strengthen assumptions
through typeclasses. Use a book-local specialization or wrapper when appropriate.
If definitions or formulations differ, prove the required bridge rather than
claiming correspondence from similar theorem names. Different proofs of the same
proposition do not require a separate proof-equality theorem.

Within a book, subsequent core developments cite its earlier independently proved
core declarations. For accepted external prerequisites, including results taught
in another book, cite Mathlib directly or through a thin book-local wrapper when
needed for the printed statement or proof index. The cross-book import prohibition
continues to apply.

If an independently developed result is later found in Mathlib, retain the local
core proof and record the corresponding Mathlib declaration. Its presence in
Mathlib is not grounds for replacing the pedagogical proof with a direct call.
Record important Mathlib correspondences in short Lean declaration docstrings
(`/-- ... -/`) beside the relevant result. Include exact declaration names and
any specialization or differences in definitions, assumptions, or conclusions.
Record principal prerequisite declarations at their use sites, including scoped
external exceptions, and identify their role as accepted prerequisites. Use a
module comment (`/-! ... -/`) once when the information applies to several
related declarations. Keep these details in Lean rather than duplicating a
correspondence inventory in the book policy; that policy owns the mathematical
permission and scope of external results. Verify declaration names against the
pinned Mathlib revision rather than guessing them. Exhaustive inventories of
elementary helper lemmas are unnecessary.

## Declaration naming

Follow [Mathlib naming conventions](https://leanprover-community.github.io/contribute/naming.html):
theorem names use `snake_case`, ordinary definitions use `lowerCamelCase`, and
types and structures use `UpperCamelCase`, subject to Mathlib's detailed rules
such as retaining the spelling of a definition embedded in a theorem name.
Keep declarations under `<Book>.ChapterNN`, where `<Book>` is the registered
`lean_module` and `NN` is the chapter number with at least two digits. Appendices
use `<Book>.AppendixNN`, with the numeric position in the appendix manifest
(`Appendix01` is printed as Appendix A). Do not
include `Textbooks` in declaration namespaces. Definitions and reusable lemmas
belong to their owning chapter too; use `private lemma` for helpers needed only
inside one file. Topic filenames do not add a required namespace level.
Use mathematical names rather than printed theorem numbers. Prefer the Mathlib
basename for a matching statement when it fits the local namespace; otherwise
name the actual hypotheses and conclusion. Avoid temporary names such as `my_`,
`textbook_`, `_proof`, or `_v2` as substitutes for mathematical meaning.

Apply these rules to new declarations. Rename existing declarations when they
are next revised for formalization, updating all uses and proof-index entries
together; documentation-only policy changes need not rename checked declarations.

## Source layout

```text
lean/
  lean-toolchain
  lakefile.toml
  lake-manifest.json
  Textbooks.lean
  Textbooks/
    ElementaryNumberTheory/
      All.lean
      Chapter02/
        DivisionAlgorithm.lean
```

From the first formalized result, every mathematical source must use
`lean/Textbooks/<Book>/ChapterNN/<Topic>.lean`. This is mandatory even when a
chapter has only one theorem. Appendix sources use the parallel
`lean/Textbooks/<Book>/AppendixNN/<Topic>.lean` layout, including from their first
result. Use descriptive `UpperCamelCase` topic filenames,
with ASCII letters and digits. Do not create a flat `ChapterNN.lean` or adopt
one file per numbered theorem. Group related definitions, supporting lemmas,
and core results by mathematical topic; one substantial theorem may constitute
an entire topic. Split a topic when its mathematical responsibilities or import
dependencies become distinct, not at an arbitrary line count.

The root `Textbooks.lean` and each book's `All.lean` are aggregation entry points,
not homes for mathematical declarations. The book-level `All.lean` is the only
exception to the chapter/topic or appendix/topic layout under a book directory.
Import topic
modules there and import earlier results as needed within the same book;
imports must remain acyclic. Do not create empty topic placeholders.

Module paths and declaration namespaces are separate. For example,
`import Textbooks.ElementaryNumberTheory.Chapter02.DivisionAlgorithm` loads
results declared in `namespace ElementaryNumberTheory.Chapter02`. Retain
`Textbooks` in filesystem paths and imports, but not in declaration names.
Moving a declaration between topic files within a chapter must preserve its
public name and proof-index link.

Lean files need not match LaTeX section files one-to-one. Stable linkage happens
at the labeled theorem level, so declaration names should describe mathematics
rather than printed theorem numbers. The proof-link checker enforces the
chapter/topic path shape and the registered declaration's book and chapter
namespace; human review checks whether a topic grouping is mathematically
coherent and whether unregistered declarations follow the namespace policy.

Set `autoImplicit false` in repository modules. Do not use `sorry`, `admit`,
or new unchecked `axiom` declarations in checked sources.

## Linking a verified proof
A verified LaTeX theorem needs two parts:

1. A repository-global theorem label such as `an1:thm:compactness`.
2. An entry in the matching chapter or appendix shard below naming its Lean
   proof declaration.

Each shard is owned by one registered book and one chapter or appendix:

| LaTeX source directory | Proof-index shard | Lean namespace |
|---|---|---|
| `books/<book>/chapters/01-topic/` | `proof-index/<book>/01-topic.yml` | `<Book>.Chapter01` |
| `books/<book>/appendices/01-topic/` | `proof-index/<book>/appendices/01-topic.yml` | `<Book>.Appendix01` |

Both shard kinds use the same entry schema:

```yaml
proofs:
  - id: an1:thm:compactness
    declaration: MathematicalAnalysis1.Chapter01.compactness
```

This is a schema example; use the actual checked declaration and label. The
shard path owns its book, chapter or appendix, and kind. Entries contain only
`id` and `declaration`; do not repeat `book`, `chapter`, `kind`, or `tex` paths.
Labels must belong to a `theorem`, `lemma`, `proposition`, or `corollary`
environment within that shard's source directory. A theorem-like label on a
section, definition, equation, or literal code sample is not a verified result.
Labels and declarations must be unique across both kinds of shard.

Appendix proofs use the same book prerequisite policy, proof roles, import
boundary, and review requirements as chapter proofs. Include appendix modules
in the owning book's `All.lean`; earlier results within that book may be reused.

## Validation commands

```sh
make check proof-links
make lean
make lean check
make check all strict
```

`make check proof-links` is a fast structural and source check without Lean. It
checks shard ownership, theorem environments, unique labels and declarations,
namespace and module paths, import reachability, and source-level `sorry`,
`admit`, and `axiom` markers. Comments and literals are excluded from that marker
check. Its result reports registered links, not kernel verification.

`make lean check` builds the pinned project and runs those checks plus a Lean
environment audit after `import Textbooks`. Each registered declaration must
exist, be safe, and have a proposition as its type. The audit rejects
repository-defined axioms, including private and unused axioms and declarations
in the root module. It also checks the transitive axiom dependencies of all
imported textbook declarations, including unregistered helpers. Only Lean's
standard `propext`, `Classical.choice`, and `Quot.sound` axioms are permitted;
`sorryAx` and other added axioms are rejected. This metatheory allowlist does not
authorize mathematical prerequisites outside a book's boundary.

The audit implementation is `scripts/lean-proof-audit.lean`, validation tooling
rather than a textbook module. The Python adapter copies it and the registered
proof requests into ignored `build/lean-links/ProofLinks.lean`. Source scanning
also catches unfinished anonymous examples that do not leave a named declaration
in the imported environment. `make check all strict` requires these checks before
building PDFs.

A passed gate establishes these formal and structural checks, not natural-language
fidelity or agreement of code copied into LaTeX. Review hypotheses, conclusions,
reasoning, and [displayed-code correspondence](#displayed-code-correspondence)
explicitly. Accepted mathematical prerequisites and the bottom-up proof order
also remain review obligations.

## Dependency updates

Dependency updates are intentional maintenance tasks. Change `LEAN_VERSION` and
`LEAN_TOOLCHAIN` together in `config/toolchain.env`, then run `make config`.
This synchronizes `lean/lean-toolchain` and the Mathlib release in
`lean/lakefile.toml`; do not edit those generated values directly. Run
`lake update` inside `lean/`, review `lean/lake-manifest.json`, then run
`make config` again to refresh the shared preface's resolved Mathlib version and
commit. Run
`make config check` and `make lean check`. Apply the shared-dependency validation
requirements in [Contributing](CONTRIBUTING.md#validation-by-change-category).
Commit the canonical configuration, synchronized consumers, and dependency lock
together. Ordinary checks must not run `lake update`.

## Scope and coverage

Do not claim that an entire textbook is formally verified merely because the
Lean project builds. Coverage is the set of entries loaded from the chapter
shards under `proof-index/`.
Material omitted pedagogically may be supplied by Mathlib and should be described
as a prerequisite at chapter or book level.
