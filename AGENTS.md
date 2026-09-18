# Repository instructions for AI agents.

## Repository purpose

This repository contains LaTeX source for several mathematics textbooks. Each
textbook lives under `books/<slug>/` and uses `book.tex` as its entry point.
Shared LaTeX definitions live under `common/styles/`, with `textbook.sty` as the
shared entry point. `books.yml` is the source of truth for the textbook list and
its build, check, release, and site flags. Each book's `chapters.yml` owns chapter and optional appendix
order, slugs, and titles; each entry's `sections.yml` owns logical section data
with one source file per logical section. The complete `book.tex` and chapter/appendix
`index.tex` files are generated from those manifests and shared templates.
CI-only Python dependencies live in `.github/requirements-ci.txt`; keep workflow
install and cache configuration pointed at that file.

## Git workflow

- Use `main` as the base for each batch of work; never commit or push directly
  to `main`. Remote `main` accepts changes only through pull requests.
- Keep local `main` aligned with `origin/main` using fast-forward updates; do
  not merge unreviewed work into it.
- Default to focused, independently revertible commits, not a separate branch
  or pull request for every request. Follow
  `docs/CONTRIBUTING.md#change-categories`; keep a theorem's exposition, Lean
  proof, and proof-index entry together, and put unrelated formatting or
  repository maintenance in separate commits.
- Choose pull request boundaries by change size, risk, and validation cost.
  Several independent commits may share one pull request when they form a
  manageable batch to review, validate, and land together. Split large or risky
  changes, or changes likely to be deferred independently, into separate pull
  requests. Account for repeated CI runs and branch-update conflicts.
- For sequential local work, accumulate focused commits on `local-work`,
  created from the synchronized `main`, and submit a manageable batch in one
  pull request. Use separate task branches when isolation is useful, and
  integrate completed work into the batch branch as needed.
  Dependent follow-up work may continue in the same batch without waiting for
  a prerequisite pull request to merge.
- After the owner merges the batch pull request, fast-forward local `main`
  to `origin/main` and recreate `local-work` from it for the next batch. Confirm
  all work is included in the merge or preserved elsewhere before removing the
  old branch; do not carry merged history forward after a squash merge.
- Validate the final combined state with all checks required by the included
  change categories. Temporary `integrate/...` branches may also be used for
  combined validation. Avoid copying changes and then adding history-only
  merges to reconnect their original branches.
- When writing commit messages, follow the repository conventions in `docs/CONTRIBUTING.md`.
- Never merge a pull request or change branch protection, Actions permissions, or secrets.
- Do not push unless the Codex interface explicitly requires it to create or update a task pull request.

## Generated and local-only files

- Do not commit generated PDFs or files under `build/`.
- Do not add ignored LaTeX auxiliary files to Git.
- Do not create placeholders for intentionally absent local-only assets.
- Preserve existing fallback logic for missing local-only files unless explicitly asked to change it.

## Editing scope

- Make the smallest change that satisfies the task.
- Preserve document structure, naming conventions, macros, and mathematical notation.
- Do not edit textbook body content unless the task explicitly requires it.
- Do not modify workflows, the devcontainer, or shared styles unless the task explicitly requires it.
- Give each logical section exactly one `NN-section-name.tex` source file;
  do not use alphabetic part suffixes or `split` metadata. Do not edit generated
  assembly or put `\chapter` or `\section` declarations in section sources.
  Run `make contents all BOOK=<slug>` after contents-manifest edits. See `docs/ARCHITECTURE.md`.
- If a shared style changes, consider and validate its effect on every textbook.

## Code readability and maintainability

- Follow `.editorconfig` and the existing language formatters: four spaces for
  Python, two spaces by default, and tabs for Make recipes; honor file-specific
  exceptions. Use `make format`
  with the appropriate `py`, `sh`, or `tex` scope; do not hand-format against it.
- Separate logical steps with blank lines. Wrap long expressions and commands
  at meaningful boundaries, without splitting literal values or changing output.
  Keep trailing whitespace absent and exactly one final newline.
- Use descriptive names, straightforward conditions, and early returns where
  they reduce nesting. Expand multi-step one-liners. Extract helpers for repeated
  logic or distinct responsibilities, not merely to shorten a function.
- Keep comments concise: explain non-obvious reasons, constraints, or invariants
  near the relevant code. Avoid document-like comment blocks, decorative banners,
  and comments that restate the code. Keep detailed guidance in `docs/`.
- Apply the same readability standards to tests and embedded scripts. Preserve
  intentional malformed fixtures and whitespace-sensitive literals.
- Preserve behavior, diagnostics, and interfaces during readability refactors.
  In TeX, Lean, YAML, shell, and templates, check that whitespace changes do not
  alter parsing, typesetting, quoting, or generated output. Edit generators rather
  than generated files, and keep displayed Lean synchronized with checked sources.
- Review all relevant languages, but leave already clear code alone. Keep
  formatting-only changes separate from structural refactors and run the checks
  required by `docs/CONTRIBUTING.md#validation-by-change-category`.

## Mathematical exposition

- For new or mathematically revised theorems selected for formalization, pair
  the mathematical statement with its Lean declaration signature and each proof
  reasoning unit with the corresponding Lean code. Follow
  `docs/writing-guide.md#paired-mathematical-exposition-and-lean-code`.
- Check Lean first, keep displayed code synchronized with the checked source,
  and review the mathematical correspondence under `docs/formalization.md`.
  Do not convert unrelated existing content as part of a documentation edit.

## Prerequisite policy documents

- Keep `books/<slug>/formalization.md` concise: accepted mathematical background,
  subjects developed in the book, and significant boundaries or scoped exceptions.
  Group routine facts by topic; name individual results when needed to distinguish
  accepted prerequisites from material the book must prove.
- Preserve mathematical scope when shortening these documents. Broad subject names
  must not silently authorize core results or stronger external theory.
- Link to `docs/formalization.md` for common proof and interface rules. Keep Lean
  API inventories, representation details, and proof recipes beside the relevant
  Lean declarations or in the exposition; use proof indexes for verified coverage.
  Do not grow prerequisite policies into implementation guides or progress reports.

## Lean source organization

- Before writing Lean code, check the project-wide `leanOptions` in
  `lean/lakefile.toml` and other applicable settings. Rely on those defaults
  instead of repeating them in individual modules.

- From the first result, put mathematical Lean sources in
  `lean/Textbooks/<Book>/ChapterNN/<Topic>.lean` (or `AppendixNN` for appendices),
  using descriptive `UpperCamelCase` topic names. Never use flat chapter files or a numbered
  theorem-per-file convention. Group related definitions and proofs by topic, using textbook sections as the
  default guide without requiring one Lean file per TeX section.
- Use `<Book>.ChapterNN` or `<Book>.AppendixNN` declaration namespaces without a
  `Textbooks` prefix.
  Keep `Textbooks` in module paths and imports. Book-level `All.lean` files are
  aggregation entry points, not mathematical sources.
- Format Lean proofs by reasoning unit: separate setup, local claims, case
  branches, and conclusions with single blank lines; indent nested proofs by
  two spaces and wrap long signatures and expressions. Keep short related tactics
  together, expand multi-step inline proofs, and keep comments brief. Apply the
  same layout to displayed Lean, preserving its checked-source correspondence.
  Keep mathematical prose outside the argument-free `lean` code environment.
  See `docs/formalization.md#lean-readability`.
- Update imports and proof-index entries together when moving or renaming
  declarations. Follow `docs/formalization.md` and run `make lean check`.

## LaTeX validation

The standard compiler is LuaLaTeX through `latexmk`; `latexmkrc` and the scripts
under `scripts/` define the supported command line. Build output belongs under
`build/<slug>/`.

Select required validation using
`docs/CONTRIBUTING.md#validation-by-change-category`. Documentation-only changes
use its focused checks; shared style changes require the complete suites.

For a single textbook, run:

```bash
make books BOOK=<slug> check strict
```

For the complete validation suites, run:

```bash
make test
make check all strict
```

A build is successful only when `latexmk` and the log checker exit successfully.
Warnings that predate the task may be reported, but do not make unrelated
changes solely to silence them.

## Validation cleanup

- Follow `docs/ARCHITECTURE.md#generated-files-and-local-outputs`: commit generated
  assembly and synchronized configuration; keep build output, site pages, and
  tool caches in their designated ignored locations.
- Before finishing, run `git status --short` when Git metadata is available.
- Never stage or commit build artifacts.

## Pull request expectations

Prepare a concise summary containing:

1. What changed.
2. Which textbooks or shared files were affected.
3. Which validation commands ran and whether they passed.
4. Any intentionally unresolved warnings or unavailable local-only files.

The repository owner performs final review and merge. GitHub Actions validate
pull requests and `main`; merged release enablement or version increases for release-enabled books trigger automatic publication
only after main CI validation gates pass. Prepare versions on development branches
with `make release-prepare BOOK=<slug> VERSION=<version>`; do not create or push
release tags locally.
