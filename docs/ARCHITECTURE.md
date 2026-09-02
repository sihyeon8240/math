# Repository architecture

## Philosophy

This repository publishes multiple independently assembled undergraduate mathematics textbooks through shared infrastructure. Each directory under `books/` owns its mathematical exposition, bibliography, metadata, and assembly order. Styles, reusable publishing templates, automation, and formal tooling are centralized so mechanical and formal improvements benefit every book consistently.

Publication independence and formal dependency are separate properties. Do not merge books or share LaTeX mathematical sections between them. Book structure is generated from book-local contents manifests. Every PDF remains independently readable and buildable, while Lean formalizations depend on the pinned Mathlib revision for foundations deliberately omitted from exposition.

Book-specific Lean modules do not directly import another textbook. Use existing Mathlib declarations for shared mathematics and keep book-specific wrapper theorems in their owning namespace. See [Lean formalization](formalization.md).

## Top-level directories

- `books/` contains each textbook's entry point, metadata, frontmatter customizations, chapters, optional appendices, and bibliography.
- `common/` contains shared publishing infrastructure: styles, assets, and reusable templates. It does not contain book-specific mathematical sections.
- `scripts/` contains repository automation for discovering, building, checking, packaging, and maintaining books.
- `docs/` contains the documentation map plus contributor, maintainer, authoring, formalization, and site-operation guidance subordinate to this architecture contract.
- `tests/` contains the Python unit-test suite for repository automation.
- `lean/` is one pinned Lake project containing book-owned formalization namespaces.
- `proof-index/<book>/<chapter>.yml` links labeled LaTeX theorems to kernel-checked Lean declarations in chapter-owned shards.
- `site/` contains website source and data.
- `.devcontainer/` defines the supported development container, while `.github/` contains CI, release, issue, and pull-request configuration.
- `build/` contains ignored, disposable Make-based output organized by book slug. The editor-only `vscode-build/` directory is also ignored and disposable.

## Book assembly and file responsibilities

```text
books.yml
    -> books/<slug>/chapters.yml
        -> chapters/<NN-name>/sections.yml
        -> appendices/<NN-name>/sections.yml
            -> NN-section-name.tex or NN-section-name-<part>.tex
```

`books.yml` registers textbooks and owns repository-level automation policy. Each book's `chapters.yml` contains the canonical ordered `chapters` list and an optional ordered `appendices` list; both entries have slugs and LaTeX titles. Each chapter or appendix `sections.yml` is the canonical ordered list of logical section slugs and LaTeX titles; a split section sets `split` to its physical source count. List position supplies the two-digit number, so numbers are not duplicated in YAML.

`make contents chap` renders each complete `book.tex` from `common/templates/book.tex`, `books.yml`, and the book's `chapters.yml`; appendices are emitted after `\backmatter`. `make contents sec` generates every chapter and appendix `index.tex`, including `\chapter`, `\section`, and literal `\input` commands. `make contents all` runs both operations; `BOOK=<slug>` limits any form to one registered book, and `check` validates without writing. `make generated` runs contents generation before site generation. Generated assembly is committed so ordinary LaTeX tools can build directly, but it must never be edited by hand.

Section source files contain mathematical content and labels only. They do not declare `\section`, load packages, or determine assembly order. A single-file logical section is named `NN-section-name.tex`; a split logical section uses `NN-section-name-a.tex`, `-b.tex`, and so on. `references.bib` and any substantive book-specific style or frontmatter overrides remain hand-maintained book-local sources. Appendix source follows the same section-only rule under `appendices/NN-name/`; its assembly is generated from the `appendices` list.

The complete `book.tex`, including its canonical manifest metadata, is generated
from the shared template and committed with the other assembly so ordinary
LaTeX tools can build directly. Book-local
`frontmatter/title-and-copyright.tex` and `frontmatter/preface.tex` files may
replace the corresponding shared presentation templates.

### Declarative contents contract

Both contents manifests use `schema_version: 1`. Slugs are nonempty lowercase hyphenated identifiers and titles are nonempty LaTeX strings. Lists must be nonempty and ordered. An optional `split` must be an integer from 2 through 26, the number of available lowercase suffixes. Unknown fields, duplicate slugs, invalid split counts, missing manifests, missing content files, orphan files, and stale generated assembly are errors.

The path rules are deterministic: chapter item `N` with slug `name` owns `chapters/NN-name/`, and appendix item `N` owns `appendices/NN-name/`; section item `N` with slug `topic` owns `NN-topic.tex`, or `NN-topic-a.tex` through the suffix implied by `split`. Rename or reorder through YAML and the corresponding content paths together, then run `make contents all`. Do not add hand-written chapter or section commands to content files.

`scripts/contents_manifest.py` is the reusable loader, validator, path mapper, and renderer. `scripts/generate-contents.py` is its command-line adapter. Source checks run generation in check mode before structural validation, README checks, and compilation.

## Shared runtime configuration

```text
config/toolchain.env       -> Docker, CI Python, Lean, and Python tooling consumers
config/container-image.txt -> local and devcontainer image consumers
```

These two files are the canonical runtime configuration. Run `make config` after editing them to synchronize format-specific consumers, including `lean/lean-toolchain`, `lean/lakefile.toml`, `.github/requirements-ci.txt`, `pyproject.toml`, and `.devcontainer/devcontainer.json`. `make config check` fails on drift. CI derives a content-addressed image tag from the canonical image inputs, prepares that image once, and passes its tested digest to downstream checks and builds. `config/container-image.txt` remains the reviewed immutable reference for local and devcontainer consumers. `make image-pin` remains a narrow automation and recovery interface so the image workflow does not depend on synchronization implementation details; routine contributors do not need to invoke it.

## Metadata and automation

```text
books.yml
    -> scripts/books.py
    -> build / check / site / release
```

`books.yml` owns each book's title, author, version, slug, short title, label prefix, optional Lean module, status, ordering, and build, check, release, and site flags. Automation consumes it through `scripts/books.py`, rather than discovering policy from README or LaTeX prose.

A book with `site: true` must also have `build: true`. Affected-book planning
combines manifest state, Git changes, and TeX dependencies; ambiguous build inputs
safely select all build-enabled books. Site publication selects only site-enabled
PDFs. Workflow files own the implementation details.

Reusable manifest policy lives in `scripts/book_manifest.py`: it loads, normalizes, validates, queries, and safely saves manifest data. `scripts/books.py` is the stable command-line adapter responsible only for argument parsing, text/JSON presentation, diagnostics, and exit codes. Python repository checks import the domain module directly; shell automation continues to use the public CLI.

The root README links to `books.yml` instead of duplicating its textbook
metadata. Site book pages remain ignored metadata-only build input generated
from the same manifest.

## What belongs where

- Mathematical exposition belongs in the owning book's section files. Never include a section from another textbook.
- Chapter and appendix order and titles belong in `chapters.yml`; section order, titles, and split counts belong in each entry's `sections.yml`.
- Generated assembly lives in the complete `book.tex` and chapter `index.tex` files; optional presentation overrides belong in the matching `frontmatter/` files.
- Book-specific preface material, references, and presentation overrides remain in the book directory and are created only when they differ from the shared defaults.
- Book-specific style extensions belong in the owning book's `local-style.sty`. Shared mathematics commands, reusable layout structure, repository-wide conventions, templates, and assets belong in `common/`.
- Repository lifecycle automation belongs in `scripts/` and is driven by `books.yml`.
- The root README points readers to `books.yml`; generated site metadata comes only from that manifest.

Shared infrastructure may be centralized, but book contents remain local. `book.tex` uses common frontmatter directly and automatically selects a book-local file when an actual `frontmatter/title-and-copyright.tex` or `frontmatter/preface.tex` override exists.

## Naming conventions

- `book.tex`: fully generated, stable compiler entry point; do not edit it directly.
- `frontmatter/title-and-copyright.tex`: optional book-local replacement for the shared title and copyright template.
- `frontmatter/preface.tex`: optional book-local replacement for the shared preface template.
- `chapters.yml`: canonical ordered chapter slugs and titles plus optional ordered appendices.
- `chapters/<NN-name>/sections.yml`: canonical ordered section slugs, titles, and optional split counts.
- `chapters/<NN-name>/index.tex`: generated chapter and section assembly; do not edit.
- `appendices/<NN-name>/sections.yml` and `index.tex`: appendix counterparts, generated after `\backmatter`.
- `NN-section-name.tex`: a single-file logical section.
- `NN-section-name-a.tex`, `NN-section-name-b.tex`, ...: the physical
  sources of one split logical section.
- `references.bib`: predictable book-local bibliography.
- `local-style.sty`: optional book-local extensions to the shared mathematics package; omit it when unused.

Numeric prefixes make reading order obvious in directory listings, while the manifests remain the authority on inclusion and order.

For section sources, `NN` is the two-digit logical section number, not a
physical-file sequence number. Logical section numbers begin at `01` and are
consecutive within a chapter. An unsplit section has exactly one unsuffixed
file. Every source of a split section shares the same `NN` and descriptive slug,
uses consecutive lowercase suffixes beginning with `-a`, and the group contains
at least two files. Thus the first split source also has `-a`; an unsuffixed
source may not be mixed with suffixed sources. A number may repeat only within
one such logical group. The generator places all parts adjacently in suffix order and logical groups in manifest order. Context-dependent names such as
`section-part-2`, `part-3`, `continuation`, and `misc` are prohibited.

For chapter and appendix directories, `NN` is a two-digit decimal number beginning at `01`.
Numbers within each list must be unique and consecutive, and `book.tex` must include chapter
indexes in increasing numeric order. The name after the number consists of lowercase
letters and digits separated by single hyphens; for example,
`chapters/01-vector-spaces/index.tex`.

### Labels

Labels are repository-global. Each book uses a short prefix, such as `nt:` for number theory, `la:` for linear algebra, and `an:` for analysis. Preserve this convention for chapters, sections, equations, theorems, and other labeled objects: it prevents collisions in repository-wide checks and makes diagnostics unambiguous. The descriptive component is hyphen-separated and may contain ASCII uppercase and lowercase letters and digits; capitalization may preserve mathematical identifiers such as `R`, `Q`, or `N`.

## Formal verification boundary

`make check all` validates both publication sources and the pinned Lean project. The matching `proof-index/<book>/<chapter>.yml` shard is the single source linking a theorem label to its Lean declaration. Checked Lean sources may not contain `sorry`, `admit`, or repository-defined `axiom` escape hatches.

The Lean project is rooted at `lean/Textbooks.lean`. Book-owned declarations belong under `lean/Textbooks/<Book>/` and the matching `Textbooks.<Book>` namespace. A book module may import Mathlib and modules owned by the same book; it may not directly import another textbook's namespace. This formal dependency structure does not change the publication boundary: each LaTeX book remains independently assembled from its own directory.

Lean verifies the registered formal statement under its explicit imports. Human review remains responsible for confirming that the formal statement faithfully represents the corresponding natural-language theorem. Verification coverage is exactly the set of registered proof-index entries, never an implicit claim about a whole book.

Detailed proof-link authoring, dependency updates, source layout, and namespace policy are documented in [Lean formalization](formalization.md).

## Stability policy

The directory layout, `books.yml` and proof-index schemas, metadata loading, chapter/index pattern, Lean dependency boundary, build scripts, automation, and CI are established interfaces. Preserve all existing commands and make the smallest compatible edit. Do not redesign these interfaces, merge books, introduce code generation, or add abstraction without a concrete maintenance benefit.
