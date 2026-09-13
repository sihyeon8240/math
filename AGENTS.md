# Repository instructions for AI agents.

## Repository purpose

This repository contains LaTeX source for several mathematics textbooks. Each
textbook lives under `books/<slug>/` and uses `book.tex` as its entry point.
Shared LaTeX definitions live under `common/styles/`, with `textbook.sty` as the
shared entry point. `books.yml` is the source of truth for the textbook list and
its build, check, release, and site flags. Each book's `chapters.yml` owns chapter and optional appendix
order, slugs, and titles; each entry's `sections.yml` owns logical section data
and an optional numeric split count. The complete `book.tex` and chapter/appendix
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
- Name single-file logical sections `NN-section-name.tex`. For split logical
  sections, keep the same number and slug and set `split` in `sections.yml` to
  the number of consecutive `-a`, `-b`, ... files. Do not edit generated
  assembly or put `\chapter` or `\section` declarations in section sources.
  Run `make contents all BOOK=<slug>` after contents-manifest edits. See `docs/ARCHITECTURE.md`.
- If a shared style changes, consider and validate its effect on every textbook.

## Mathematical exposition

- For new or mathematically revised theorems selected for formalization, pair
  the mathematical statement with its Lean declaration signature and each proof
  reasoning unit with the corresponding Lean code. Follow
  `docs/writing-guide.md#paired-mathematical-exposition-and-lean-code`.
- Check Lean first, keep displayed code synchronized with the checked source,
  and review the mathematical correspondence under `docs/formalization.md`.
  Do not convert unrelated existing content as part of a documentation edit.

## Lean source organization

- From the first result, put mathematical Lean sources in
  `lean/Textbooks/<Book>/ChapterNN/<Topic>.lean` (or `AppendixNN` for appendices),
  using descriptive `UpperCamelCase` topic names. Never use flat chapter files or a numbered
  theorem-per-file convention. Group related definitions and proofs by topic.
- Use `<Book>.ChapterNN` or `<Book>.AppendixNN` declaration namespaces without a
  `Textbooks` prefix.
  Keep `Textbooks` in module paths and imports. Book-level `All.lean` files are
  aggregation entry points, not mathematical sources.
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
pull requests and `main`; tag workflows create releases only after their own
validation gates pass.
