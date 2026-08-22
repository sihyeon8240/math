# Contributing

Thank you for helping improve these textbooks. Keep mathematical-content changes separate from repository maintenance whenever possible.

## Reporting errors

Open a GitHub Issue for typographical errors, mathematical errors, missing citations, broken references, or build failures. Include:

- the textbook and chapter or section;
- the source path or PDF page when known;
- the current statement;
- the proposed correction and mathematical justification.

Use a Pull Request for a focused correction after checking that an Issue does not already cover it. Discuss a new chapter, major reorganization, notation change, or shared-style redesign in an Issue before implementation.

## Development checks

After preparing the dependencies documented in the root README, run `make help` for a concise command summary and `make doctor env` to check the environment. Use `make format all` to format LaTeX and Python sources, or `make format {tex|py} check` for a focused non-mutating check. See [Formatting](developer-workflow.md#formatting) for the exact file scope, tool behavior, and CI split. Use `make books BOOK=<slug>` for one registered book, `make books` for the manifest bulk-build set, `make lean check` for focused formal verification, and `make check all strict` for the complete Lean and LaTeX validation. Book registration and bulk participation are controlled by `books.yml`; do not bypass it. Site publication metadata is also manifest-owned: run `make site check` before submitting; `make site` is needed only to prepare a local Jekyll build.

Formal proofs follow [the Lean formalization policy](formalization.md). Keep book modules independent, put only genuinely shared adapters in Foundation, and register a `\leanverified{...}` marker in the matching `proof-index/<book>/<chapter>.yml` shard only after reviewing the correspondence between the natural-language and Lean statements.

To update the immutable textbook build image in the devcontainer and CI workflows, run `make image-pin DIGEST=<64-character-sha256>`; the command validates the digest and verifies every consumer after updating them.

## Pull requests

Every PR must compile and should run both independent validation suites:

    make test
    make check all strict

Describe affected books, validation performed, source or rights information for new material, and any intentionally unresolved warnings. Do not commit build or dist output.

## Copyright and sources

- Do not submit text, problems, solutions, or figures whose copyright status is unclear.
- Cite external sources appropriately when they informed a contribution.
- Distinguish mathematical facts from a particular author's wording or exposition.
- Do not include lecture notes, assignments, examinations, or solution manuals that you do not have permission to publish.
- Confirm the source and publication rights of every new axiom, theorem exposition, proof, figure, and exercise.
- AI-generated material must be checked by a human for mathematical correctness, provenance, and licensing. Do not submit unverified generated results verbatim.

## File naming

- Use lowercase English names with hyphens.
- Book slugs contain no year, semester, or instructor name.
- Chapter directories use NN-meaningful-title.
- Chapter entry points are index.tex.
- Section files use NN-meaningful-title.tex.
- Read the actual LaTeX heading before naming a file; do not infer an uncertain title.
- Put shared assets under common/assets and book-only assets under books/<slug>/figures.

## Labels

New labels use:

    <book-prefix>:<kind>:<hyphenated-description>

Book prefixes are la, an, and nt. Supported kinds include ch, sec, ax, def, thm, lem, prop, cor, ex, exc, eq, fig, and tab. Examples:

    la:thm:rank-nullity
    an:ax:completeness
    an:def:compactness
    an:thm:R-is-uncountable

Descriptions may contain ASCII uppercase and lowercase letters, digits, and single
hyphens. Preserve meaningful capitalization in mathematical identifiers such as
`N`, `Z`, `Q`, `R`, `C`.

Legacy labels are retained until references can be migrated safely in one coordinated change.

See `writing-guide.md` for the section-writing checklist, environment
semantics, examples of the label policy, and the public-PDF behavior of draft
annotations.

## Starting a new textbook

Run `make new-book SLUG=<slug> TITLE="<title>"`. It copies the files in
`common/templates/` and registers the new book in `books.yml` as a draft. The
script never overwrites an existing directory. Assign a label prefix, review the
generated metadata and README, then run:

    make check manifest
    make readme root
    make readme books BOOK=<slug>
    make books BOOK=<slug>
    make check all strict

CI build and release matrices are generated from `books.yml`; set the manifest
flags deliberately when the new book is ready for those workflows. To publish it on the site, set `site: true` and run `make site check BOOK=<slug>`. The Pages job generates the ignored metadata-only page before Jekyll runs; do not commit files under `site/books/`.
Book README detail sections are also generated; after changing chapter or appendix
assembly, titles, or `references.bib`, run `make readme books BOOK=<slug>` instead of editing the
generated chapters, appendices, references, or build/feedback help.

## Releases

Each book version is defined by exactly one `\newcommand{\version}{X.Y.Z}` macro in `books/<slug>/metadata.tex`. Individual release tags use `<slug>-v<version>` and must match it exactly. Official releases include only books with `release: true`.

For an official release, first merge and push the reviewed commit to `main`, then run `make publish BOOK=<slug>` from a clean local `main` checkout whose `HEAD` exactly matches fetched `origin/main`. The command never publishes source code. It builds and packages locally in a temporary directory, creates and pushes an annotated tag, waits with a timeout for the matching Actions run, and uploads the PDF and `SHA256SUMS` without overwriting assets. GitHub Actions validates tags and creates Releases but never builds or uploads official release PDFs.

## Commit messages

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
    style(common): unify theorem environment spacing
    ci(release): validate tags against textbook metadata

## Repository architecture and metadata

Read [the architecture guide](ARCHITECTURE.md) before structural or metadata work. `books.yml` owns repository title, short title, status, order, and build/check/release/site participation. `metadata.tex` owns LaTeX-facing titles, version, slug and PDF title metadata. README files are human-facing and are never parsed for site content; site pages intentionally contain no separate book descriptions. Descriptive title differences produce warnings, while missing files, invalid slug/version declarations, and broken assembly links fail validation.

## Adding a chapter or section

Create a chapter at `books/<slug>/chapters/NN-descriptive-name/index.tex`. It declares exactly one `\chapter`, includes numbered section files in order, and is included once from `book.tex`. Add sections beside it as `NN-section-name.tex`, containing mathematical content and a section heading but no document setup. Run `make books BOOK=<slug>` and `make check all strict`; checks reject missing targets, duplicate includes, and orphan chapter or section files.

## Completing a new book

After `make new-book SLUG=<slug> TITLE="<title>"`, replace scaffold placeholders and review `book.tex`, `metadata.tex`, `README.md`, `references.bib`, `local-style.sty`, and the initial chapter. Set the version, slug, display/PDF titles, any book-specific style extensions, and a unique label prefix. Keep the registry title and README heading aligned and set manifest flags deliberately.

The scaffold assigns a unique label prefix from the slug, creates the standard frontmatter wrappers and bibliography file, and regenerates the book README. If the suggested prefix collides, choose an explicit unique `label_prefix` in `books.yml` and rerun validation.

## Releasing a version

Update the single `\version` declaration, document the change when appropriate, and run `make check all strict`. After the change reaches `main`, the repository owner publishes it with `make publish BOOK=<slug>`; do not bypass release flags or overwrite release assets.

See [developer-workflow.md](developer-workflow.md) for supported development, review, CI, and release commands.
