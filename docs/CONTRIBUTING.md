# Contributing

Thank you for helping improve these textbooks. Keep mathematical-content changes separate from repository maintenance whenever possible.

## Contribution workflow

### Reporting errors

Open a GitHub Issue for typographical errors, mathematical errors, missing citations, broken references, or build failures. Include:

- the textbook and chapter or section;
- the source path or PDF page when known;
- the current statement;
- the proposed correction and mathematical justification.

Use a Pull Request for a focused correction after checking that an Issue does not already cover it. Discuss a new chapter, major reorganization, notation change, or shared-style redesign in an Issue before implementation.

### Development checks

Use the public Make interface described in the [developer workflow](developer-workflow.md).
Before review, run the affected book build and both validation suites shown below.
Formal proof contributions must also follow the [Lean formalization policy](formalization.md).

### Pull requests

Before review, run both independent validation suites:

    make test
    make check all strict

If either command cannot run locally, explain why in the PR. Describe affected
books, validation performed, source or rights information for new material, and
any intentionally unresolved warnings. Do not commit build or dist output.

## Contribution policies

### Copyright and sources

- Do not submit text, problems, solutions, or figures whose copyright status is unclear.
- Cite external sources appropriately when they informed a contribution.
- Distinguish mathematical facts from a particular author's wording or exposition.
- Do not include lecture notes, assignments, examinations, or solution manuals that you do not have permission to publish.
- Confirm the source and publication rights of every new axiom, theorem exposition, proof, figure, and exercise.
- AI-generated material must be checked by a human for mathematical correctness, provenance, and licensing. Do not submit unverified generated results verbatim.

### Authoring conventions

File naming, labels, environments, and textbook prose conventions are maintained
in the [textbook writing guide](writing-guide.md). Structural ownership and the
generated-file boundary are defined by the [architecture guide](ARCHITECTURE.md).

#### Blank lines and end-of-file newlines

Use one empty line between semantic blocks and do not add multiple consecutive
empty lines for visual spacing. Language syntax and the configured formatter
take precedence when they require a different number of empty lines, such as
between top-level Python declarations.

Every text source file must end with exactly one line-feed character, with no
additional empty line at the end. Keep blank lines empty; the repository-wide
EditorConfig settings remove trailing whitespace.

## Task-specific workflows

### Starting a new textbook

Follow [Book structure and manifests](writing-guide.md#book-structure-and-manifests).
Review the generated sources and manifest record before enabling automation flags;
site publication settings and checks are documented in [Site metadata](site-metadata.md).

### Releases

Release eligibility and the post-merge publication procedure are documented in
the [developer workflow](developer-workflow.md#releases).

### Structural changes

Read [the architecture guide](ARCHITECTURE.md) before changing repository structure
or metadata. For chapter and section authoring, follow the manifest-driven workflow
in the [textbook writing guide](writing-guide.md#book-structure-and-manifests);
do not edit generated `book.tex` or `index.tex` files.

## Change classification and validation

### Change categories

Classify each change by its primary responsibility and keep unrelated categories
in separate pull requests or commits:

| Category | Typical scope |
|---|---|
| Mathematical content | One textbook's section sources, appendices, bibliography, and mathematically meaningful local notation |
| Typesetting and presentation | Shared styles and templates, book- and site-specific presentation assets, typography, and PDF behavior |
| Formal verification | Lean sources, proof-index entries, and the correspondence between formal declarations and labeled textbook statements |
| Repository engineering | Scripts, tests, Make targets, configuration, CI, release automation, and site generation |

Change categories describe review ownership and rollback boundaries; commit
types describe the nature of a change. For example, a repository-engineering
change may use `fix`, `refactor`, `build`, `ci`, `test`, or `chore` depending on
what the commit does.

Typesetting and presentation is the publishing category for visual output. It
does not include release tagging, packaging, uploads, or their automation, which
are repository engineering. Classify a change by its effect rather than its file
extension: mathematical exposition and mathematically meaningful notation remain
mathematical content even when they live in `.tex` or `.sty` files, while fonts,
spacing, environment presentation, and page behavior are typesetting.

Separate changes when they have different review criteria, failure modes, or
rollback boundaries. In particular, do not combine mathematical revisions with
unrelated automation refactors, semantic edits with repository-wide formatting,
or dependency upgrades with new formal proofs.

Changes from multiple categories may remain together when they are necessary to
complete one coherent result. Examples include a theorem label with its Lean
proof and proof-index entry, a contents-manifest edit with the corresponding file
moves and generated assembly, and an automation fix with its regression test and
documentation. A useful test is whether reverting only part of the change would
leave the repository correct and meaningful; if not, keep the required parts
together.

Within mathematical content, treat each textbook as an independent change
boundary unless one shared typesetting change intentionally affects multiple
books. Validate shared typesetting and repository-engineering changes against
every affected textbook.

Use the following boundaries for cases that can appear to span categories:

- site generators, generated metadata, deployment code, and CI integration are
  repository engineering; site typography and presentation assets are
  typesetting and presentation changes;
- book-local presentation configuration is typesetting and presentation, while
  canonical toolchain, dependency, build, and automation configuration is
  repository engineering; and
- classify dependency upgrades as repository engineering, then choose `build`
  or `ci` as the commit type according to the dependency's consumer.

### Validation by change category

#### Typesetting and presentation

Use focused checks while developing, then run the complete validation suites
before review. Check the rendered PDF visually when a change can affect fonts,
spacing, page breaks, bookmarks, links, or other behavior that automated checks
cannot fully assess.

| Change | Focused validation |
|---|---|
| Book-local presentation or typography | `make format tex check` and `make books BOOK=<slug> check` |
| Shared styles or templates | `make format tex check` and `make books check strict` |
| Contents manifests or generated LaTeX assembly | `make contents all check BOOK=<slug>` and `make books BOOK=<slug> check` |
| PDF bookmarks, references, fonts, or page behavior | `make books [BOOK=<slug>] check [strict]` and visual PDF review |

Changes under `common/styles/` or to the shared book template affect every
build-enabled textbook. A book-local frontmatter or presentation change affects
that book. Treat a common input with uncertain consumers as affecting every
build-enabled textbook.

#### Repository engineering

Use the narrow checks while developing, then run the complete validation suites
before review. The following commands are the minimum focused checks for common
repository-engineering changes:

| Change | Focused validation |
|---|---|
| Python scripts or tests | `make format py check`, `make test`, and `make check source` |
| Make or shell automation | `make format sh check`, `make test`, and `make check source` |
| Shared configuration or dependencies | `make config check` and `make check all strict` |
| Site generation | `make site check` and `make test` |
| Build inputs or shared infrastructure | affected book builds and `make check all strict` |
| CI or release automation | relevant regression tests and `make check source` |

`make check source` does not run formatters or linters. Run the relevant
`make format {tex|py|sh|all} check` command separately when a change touches files
covered by those tools.

For textbook validation, book-local inputs affect that book. Shared styles and
common build inputs affect every book that consumes them; ambiguous build inputs
affect every build-enabled book. Documentation-only and CI-only changes may not
require a PDF build when they cannot affect textbook output. The affected-book
planner in CI applies these same rules conservatively.

## Commit conventions

Keep each commit focused on one logical change. Separate textbook content from
repository maintenance, and separate formatting-only changes from semantic
changes. Include tests and documentation required by a change in the same
commit. Every commit should leave the repository in a buildable state and be
safe to revert independently. Never include generated PDFs, `build/`, or LaTeX
auxiliary files.

Write commit subjects in this form:

    <type>(<scope>): <summary>

Use a lowercase type and scope, no space before the opening parenthesis, and a
lowercase imperative summary without a trailing period. Keep the subject to 72
characters when practical. Use a body when the reason or impact is not clear
from the subject; explain why the change is needed rather than repeating the
diff.

Supported types are:

- `content` for textbook definitions, theorems, proofs, examples, and prose;
- `fix` for defects in source, tooling, or automation;
- `docs` for contributor and repository documentation;
- `refactor` for structural changes that preserve behavior and meaning;
- `style` for formatting-only changes;
- `build` for Make, LaTeX build, dependency, and packaging configuration;
- `ci` for GitHub Actions and other continuous-integration changes;
- `test` for validation and test code; and
- `chore` for maintenance that does not fit another type.

Use a textbook slug or a stable repository component as the scope, written in
lowercase kebab-case. Use `common` for shared textbook resources and `repo` for
repository-wide changes. Avoid vague summaries such as `update files`, `revise
content`, or `misc fixes`.

Examples:

    content(analysis): clarify the definition of uniform continuity
    fix(number-theory): correct the hypothesis of Euler's theorem
    build(makefile): preserve argument order in help output
    docs(contributing): document textbook validation steps
    style(common): normalize latex source indentation
    fix(common): correct theorem environment spacing
    refactor(common): centralize title-page typography
    ci(release): validate tags against textbook metadata
