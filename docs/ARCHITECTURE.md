# Repository architecture

## Philosophy

This repository publishes multiple independently assembled undergraduate mathematics textbooks through shared infrastructure. Each directory under `books/` owns its mathematical exposition, bibliography, metadata, and assembly order. Styles, reusable publishing templates, automation, and a formal foundation layer are centralized so mechanical and formal improvements benefit every book consistently.

Publication independence and formal dependency are separate properties. Do not merge books, share LaTeX mathematical sections between them, or generate book structure. Every PDF remains independently readable and buildable, while Lean formalizations may depend on the pinned Mathlib revision and `Textbooks.Foundation` for foundations deliberately omitted from exposition.

Book-specific Lean modules do not directly import another textbook. Prefer an existing Mathlib theorem; otherwise promote genuinely shared notation or interoperability lemmas to the thin Foundation layer. See [Lean formalization](formalization.md).

## Top-level directories

- `books/` contains each textbook's entry point, metadata, frontmatter customizations, chapters, optional appendices, and bibliography.
- `common/` contains shared publishing infrastructure: styles, assets, and reusable templates. It does not contain book-specific mathematical sections.
- `scripts/` contains repository automation for discovering, building, checking, packaging, and maintaining books.
- `docs/` contains the documentation map plus contributor, maintainer, authoring, formalization, and site-operation guidance subordinate to this architecture contract.
- `tests/` contains the Python unit-test suite for repository automation.
- `lean/` is one pinned Lake project containing the shared formal foundation and book-owned namespaces.
- `proof-index/<book>/<chapter>.yml` links labeled LaTeX theorems to kernel-checked Lean declarations in chapter-owned shards.
- `site/` contains website source and data.
- `.devcontainer/` defines the supported development container, while `.github/` contains CI, release, issue, and pull-request configuration.
- `build/` contains ignored, disposable Make-based output organized by book slug. The editor-only `vscode-build/` directory is also ignored and disposable.

## Book assembly and file responsibilities

```text
book.tex
    -> metadata.tex
    -> frontmatter
    -> chapters/<NN-name>/index.tex
    -> NN-section-name.tex or NN-section-name-<part>.tex files
    -> bibliography
```

Optional appendices may follow the main chapters; no book is required to have them. The `chapters/<NN-name>/index.tex` layer intentionally keeps a chapter declaration and section order together. Do not flatten it.

- `book.tex` is the document entry point. It selects the document class, loads shared `textbook.sty` and then the book-local `local-style.sty`, configures the bibliography, loads metadata, includes frontmatter and chapters (and optional appendices), and prints the bibliography. Nothing else belongs there.
- `local-style.sty` owns book-specific additions and is loaded after the shared mathematics package. Shared mathematics packages, operators, symbols, and delimiter commands remain in `common/styles/textbook-math.sty`.
- `metadata.tex` holds concise, book-local LaTeX configuration: version, slug, display title, LaTeX title, author declaration, PDF metadata, and any frontmatter template overrides. It contains no chapters or long-form text.
- `chapters/<NN-name>/index.tex` declares one chapter, includes its section files, and determines their order. It contains no document setup.
- Section source files contain actual mathematical content only and no document setup. A single-file logical section is named `NN-section-name.tex`. At roughly 30--50 pages, a logical section should be split into alphabetically suffixed source files that retain the same logical section number and slug. This is guidance, not an automatic check.
- `references.bib` is the book-local bibliography database.
- Each book's `README.md` is the human-facing introduction, not repository metadata. Its marked detail section is generated for every book by `make readme books`, or for one book by `make readme books BOOK=<slug>`: numbered chapters and unnumbered appendices come from the canonical `book.tex` assembly and chapter declarations, references come from `references.bib`, and build/feedback help comes from the registered slug and shared template. Edit neither that generated section nor its markers directly. Site book pages are ignored, metadata-only build input generated from `books.yml`; their front matter is the site's only generated metadata representation, with no committed page or separate Jekyll data copy. No automation may parse or depend on README prose.
- The root `README.md` introduces the repository; detailed policy belongs here.
- `books.yml` is the canonical repository metadata registry and ordered textbook list.

### Static assembly syntax contract

Assembly relationships in every `book.tex` and `chapters/<NN-name>/index.tex` must use literal, statically visible `\input{path}` or `\include{path}` commands. Both extensionless paths and paths ending in `.tex` are supported, for example:

```tex
\include{chapters/01-vector-spaces/index}
\input{chapters/01-vector-spaces/01-definitions.tex}
```

Do not construct assembly paths through macros, loops, conditionally computed values, `\csname`, filesystem discovery, or generated chapter/section lists. In particular, forms such as `\input{\somecomputedpath}` and wrapper macros that synthesize an `\include` path are unsupported. Remove obsolete include lines instead of leaving them commented out; Git history preserves them.

This explicit syntax makes source order human-readable and lets `scripts/check-architecture.py` statically recover the real assembly graph. The checker relies on this contract to detect orphaned, duplicate, missing, or incorrectly ordered chapters and sections consistently in local and CI checks. It is intentionally a small structural checker, not a complete TeX parser.

## Metadata and automation

```text
books.yml
    -> scripts/books.py
    -> build / check / site / release
```

`books.yml` owns repository-level title, short title, label prefix, optional Lean module, status, ordering, and build, check, release, and site flags. Automation consumes it through `scripts/books.py`, rather than discovering policy from README or LaTeX prose.

A book with `site: true` must also have `build: true`. `scripts/affected-books.py` combines manifest state, Git changes, book-local source ownership, and recursively resolved TeX/style dependencies. Known site, documentation, and template changes do not trigger PDF builds; unclassified build-relevant changes safely select all build-enabled books. Pages publishes only `site: true` PDFs from the complete `generated-pdfs` branch snapshot at `/pdf/<slug>.pdf`; build-enabled, site-disabled books may still produce CI artifacts.

Reusable manifest policy lives in `scripts/book_manifest.py`: it loads, normalizes, validates, queries, and safely saves manifest data. `scripts/books.py` is the stable command-line adapter responsible only for argument parsing, text/JSON presentation, diagnostics, and exit codes. Python repository checks import the domain module directly; shell automation continues to use the public CLI.

`metadata.tex` has a complementary LaTeX-facing role. Keep `\version` and `\slug` there because automation intentionally reads them. It also owns display and LaTeX titles, the author declaration, and PDF metadata. Do not replace it with YAML or move version and slug elsewhere. Where a concept appears in both places, `books.yml` governs repository operations, including the globally unique `label_prefix` and optional `lean_module`, and `metadata.tex` supplies its typeset/PDF representation.

## What belongs where

- Mathematical exposition belongs in the owning book's section files. Never include a section from another textbook.
- Chapter declaration and section order belong in that chapter's `index.tex`.
- Assembly belongs in `book.tex`; concise book-local LaTeX configuration belongs in `metadata.tex`.
- Book-specific preface material, references, and license overrides remain in the book directory.
- Book-specific style extensions belong in the owning book's `local-style.sty`. Shared mathematics commands, reusable layout structure, repository-wide conventions, templates, and assets belong in `common/`.
- Repository lifecycle automation belongs in `scripts/` and is driven by `books.yml`.
- Human-facing README prose is never a site automation input. Site metadata comes only from `books.yml`.

Shared infrastructure may be centralized, but book contents remain local. Common templates may provide frontmatter layout or repository-wide notation conventions while every book retains a local frontmatter file as its inclusion and customization point.

## Naming conventions

- `book.tex`: stable compiler entry point.
- `metadata.tex`: predictable automation-readable and LaTeX-facing metadata.
- `chapters/<NN-name>/index.tex`: chapter declaration and ordered section list.
- `NN-section-name.tex`: a single-file logical section.
- `NN-section-name-a.tex`, `NN-section-name-b.tex`, ...: the physical
  sources of one split logical section.
- `references.bib`: predictable book-local bibliography.
- `local-style.sty`: book-local extensions to the shared mathematics package.

Numeric prefixes make reading order obvious in directory listings, while `index.tex` remains the explicit authority on inclusion and order.

For section sources, `NN` is the two-digit logical section number, not a
physical-file sequence number. Logical section numbers begin at `01` and are
consecutive within a chapter. An unsplit section has exactly one unsuffixed
file. Every source of a split section shares the same `NN` and descriptive slug,
uses consecutive lowercase suffixes beginning with `-a`, and the group contains
at least two files. Thus the first split source also has `-a`; an unsuffixed
source may not be mixed with suffixed sources. A number may repeat only within
one such logical group. In `index.tex`, all parts are adjacent, in suffix order,
and logical groups appear in numeric order. Context-dependent names such as
`section-part-2`, `part-3`, `continuation`, and `misc` are prohibited.

For chapter directories, `NN` is a two-digit decimal number beginning at `01`.
Chapter numbers must be unique and consecutive, and `book.tex` must include chapter
indexes in increasing numeric order. The name after the number consists of lowercase
letters and digits separated by single hyphens; for example,
`chapters/01-vector-spaces/index.tex`.

## Labels

Labels are repository-global. Each book uses a short prefix, such as `nt:` for number theory, `la:` for linear algebra, and `an:` for analysis. Preserve this convention for chapters, sections, equations, theorems, and other labeled objects: it prevents collisions in repository-wide checks and makes diagnostics unambiguous. The descriptive component is hyphen-separated and may contain ASCII uppercase and lowercase letters and digits; capitalization may preserve mathematical identifiers such as `R`, `Q`, or `N`.

## Formal verification boundary

`make check all` validates both publication sources and the pinned Lean project. A `\leanverified{...}` marker is valid only when its theorem label and Lean declaration are registered in the matching `proof-index/<book>/<chapter>.yml` shard. Checked Lean sources may not contain `sorry`, `admit`, or repository-defined `axiom` escape hatches.

The Lean project is rooted at `lean/Textbooks.lean`. Shared declarations belong under `lean/Textbooks/Foundation.lean` or its subordinate Foundation modules, while book-owned declarations belong under `lean/Textbooks/<Book>/` and the matching `Textbooks.<Book>` namespace. A book module may import Mathlib, Foundation, and modules owned by the same book; it may not directly import another textbook's namespace. This formal dependency structure does not change the publication boundary: each LaTeX book remains independently assembled from its own directory.

Lean verifies the registered formal statement under its explicit imports. Human review remains responsible for confirming that the formal statement faithfully represents the corresponding natural-language theorem. Verification coverage is exactly the set of registered proof-index entries, never an implicit claim about a whole book.

Detailed proof-link authoring, dependency updates, source layout, and Foundation promotion criteria are documented in [Lean formalization](formalization.md).

## Stability policy

The directory layout, `books.yml` and proof-index schemas, metadata loading, chapter/index pattern, Lean dependency boundary, build scripts, automation, and CI are established interfaces. Preserve all existing commands and make the smallest compatible edit. Do not redesign these interfaces, merge books, introduce code generation, or add abstraction without a concrete maintenance benefit.
