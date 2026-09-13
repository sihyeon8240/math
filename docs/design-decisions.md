# Design decisions

This records why established choices fit this repository; [the architecture guide](ARCHITECTURE.md) defines the choices themselves. None is claimed to be universally optimal.

## Content boundaries

### Independent textbooks and unshared mathematics

- **Decision:** each book owns all exposition.
- **Motivation:** readers and releases must stand alone.
- **Benefits:** clear provenance, local revision, and no hidden coupling.
- **Tradeoff:** repeated explanations can drift.
- **Future direction:** improve diagnostics, not cross-book includes.

### Shared infrastructure

- **Decision:** styles, templates, and automation are common.
- **Motivation:** publishing mechanics are genuinely repository-wide.
- **Benefits:** consistent output and fewer fixes.
- **Tradeoff:** a shared change has a broad blast radius.
- **Future direction:** validate every book after common changes.

## Assembly and metadata

### Manifest-owned metadata

- **Decision:** `books.yml` owns repository and publication metadata; generated
  TeX and site projections consume that single record.
- **Motivation:** release, site, and TeX consumers should agree without parsing prose.
- **Benefits:** one automation registry and no duplicated metadata.
- **Tradeoff:** generated projections must be regenerated and checked for drift.
- **Future direction:** add fields only for real consumers and preserve strict checks.

### Declarative book contents

- **Decision:** each book's `chapters.yml` orders chapters and each chapter's `sections.yml` orders logical sections; generated complete `book.tex` files and `index.tex` files provide literal LaTeX assembly.
- **Benefits:** titles and order have one machine-readable source, while committed generated assembly remains inspectable.
- **Tradeoff:** contributors must regenerate after manifest edits.
- **Future direction:** extend the schema only when a real cross-consumer need appears.

### Optional appendices

- **Decision:** books opt in; numbered appendices A, B, ... precede backmatter
  and support the same proof-link checks as chapters.
- **Benefits:** structure follows subject needs.
- **Tradeoff:** automation must tolerate both shapes.
- **Future direction:** keep appendix assembly manifest-owned.

### Metadata-only site pages

- **Decision:** site detail pages use `books.yml` for publication metadata and theorem sources
  plus the proof index for Lean coverage; there is no separately maintained description.
- **Benefits:** no descriptive drift or hidden README automation contract.
- **Tradeoff:** the PDF and source remain the authoritative subject detail.
- **Future direction:** keep site metadata manifest-owned.

## Publishing and site generation

### Ephemeral release staging

- **Decision:** development builds remain under ignored `build/`; release packaging
  uses an automatically cleaned temporary directory. Uploads remain in a draft
  until the owner reviews and publishes the release.
- **Benefits:** no persistent staging state and a narrower public interface.
- **Tradeoff:** local release artifacts exist only on GitHub after upload.
- **Future direction:** preserve asset immutability.

### Ephemeral manifest-derived site pages

- **Decision:** site metadata is generated into ignored book-page front matter immediately before Jekyll runs; there is no committed page or separate Jekyll data copy.
- **Benefits:** source-only diffs and one canonical registry.
- **Tradeoff:** local Jekyll builds require a generation step.
- **Future direction:** retain non-mutating render checks.

## Customization and shared infrastructure

### Optional local overrides

- **Decision:** books use shared frontmatter and styles directly unless a substantive local override file exists.
- **Benefits:** no empty placeholders or pass-through wrappers, while customization remains available.
- **Tradeoff:** optional-file loading is part of the stable `book.tex` template.
- **Future direction:** create overrides only when a book actually differs.

### Unicode-math and code fonts

- **Decision:** retain the existing mathematical typesetting stack for now.
  Centralize Lean text-font fallback in `textbook-code.sty`; do not add
  `unicode-math` separately to a book preamble to fix code glyphs.
- **Reason:** a `lean` block is literal text rendered by `minted` and `fontspec`.
  Its missing glyphs need a text-font fallback. `unicode-math` instead selects
  OpenType fonts for mathematical mode; it does not configure the code font.
  See the [package overview](https://ctan.org/pkg/unicode-math).
- **Potential benefit:** a deliberate migration could align the mathematical
  font with TeX Gyre Termes body text and support literal Unicode mathematical
  input. The existing source-macro convention can still be retained.
- **Compatibility cost:** the shared stack currently loads `amssymb`, `bm`,
  `mathrsfs`, and `mathtools`. A migration must review bold symbols and
  expressions, the distinction between calligraphic and script alphabets,
  delimiters, accents, and package load order. The
  [upstream manual](https://github.com/latex3/unicode-math/blob/master/um-doc-main.tex)
  distinguishes symbol alphabets from text alphabets and notes that the
  `sym` commands do not replace all the capabilities of `bm`.

A local comparison on 2026-09-12 used the repository's LuaLaTeX toolchain,
`unicode-math` 0.8r (2023-08-13), and `texgyretermes-math.otf` with
`math-style=TeX,bold-style=TeX`. The existing preamble compiled the sample.
Adding `unicode-math` produced an `Improper alphabetic constant` error for
`\bm{\alpha}`. Isolated probes confirmed that `\bm{x}` and
`\mathcal{ABC}\quad\mathscr{ABC}` compiled, while `\bm{\alpha}` failed.
The trial also reported `mathtools` command overrides and a script-font shape
substitution. These results establish that simply appending the package is not
a compatible migration; they do not imply that a planned migration is impossible.

To reproduce the failing case in a document using the repository's shared
style search path:

```tex
\documentclass{book}
\usepackage{textbook}
\usepackage[math-style=TeX,bold-style=TeX]{unicode-math}
\setmathfont{texgyretermes-math.otf}
\begin{document}
$\bm{\alpha}$
\end{document}
```

A future migration should first choose the mathematical font and alphabet
semantics, then adapt the shared macros and their consumers, compare representative
formulas and all book PDFs, and pass both complete validation suites. It must
preserve meaningful distinctions such as `\mathcal` versus `\mathscr`; replacing
all `\bm` calls mechanically with `\symbf` is insufficient. The
[font and Unicode authoring policy](writing-guide.md#fonts-and-unicode) applies
independently to Lean code before and after such a migration.

## Build and validation architecture

### Thin build scripts

- **Decision:** scripts compose manifest queries, `latexmk`, and log checks.
- **Benefits:** understandable failures and replaceable layers.
- **Tradeoff:** several small entry points.
- **Future direction:** keep Make targets as the contributor interface.

### Layered validation

- **Decision:** manifest, source, label, build, and log checks remain separate.
- **Benefits:** focused diagnostics and cheap early failures.
- **Tradeoff:** overlap and more commands.
- **Future direction:** improve messages rather than merge layers.

## Repository-wide conventions

### Book-prefixed labels

- **Decision:** each book uses its manifest-owned `label_prefix` to prevent repository-global collisions.
- **Benefits:** unambiguous references.
- **Tradeoff:** longer labels and legacy migration.
- **Future direction:** migrate only in coordinated, verified changes.

### Independent formal dependencies

- **Decision:** book Lean modules use Mathlib and their own book modules, without direct cross-book imports.
- **Benefits:** each book can evolve its formal prerequisites independently.
- **Tradeoff:** results absent from Mathlib may need separate local proofs.
- **Future direction:** retain this boundary at the current scale; reconsider only when concrete duplication costs justify a policy review.

### Paired mathematical exposition and formal code

- **Decision:** new or mathematically revised theorems selected for formalization
  pair their statements and proof reasoning units with corresponding Lean code,
  as defined in the [writing guide](writing-guide.md#paired-mathematical-exposition-and-lean-code).
- **Motivation:** readers should be able to relate a readable mathematical
  argument to its formal implementation at each substantive step.
- **Benefits:** local correspondence makes assumptions and proof reasoning
  easier to review while preserving an explanation readable without the code.
- **Tradeoff:** displayed fragments duplicate checked source and require explicit
  synchronization and review; checking the Lean project does not check the copy.
- **Future direction:** migrate existing exposition during relevant mathematical
  revisions while preserving each book's independent prerequisite boundary.

### Documented policies

- **Decision:** stable contracts are written down.
- **Benefits:** consistent human and AI work.
- **Tradeoff:** documents need maintenance.
- **Future direction:** cross-reference instead of copying policy text.
