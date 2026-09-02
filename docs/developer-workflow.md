# Developer workflow

This guide describes ordinary repository operations. [the architecture guide](ARCHITECTURE.md) remains authoritative for structure and metadata ownership.

## Development environment

The publishing compiler is LuaLaTeX through `latexmk`. Tool versions are owned by
`config/toolchain.env`, the immutable development and CI image is owned by
`config/container-image.txt`, and Lean uses `lean/lean-toolchain` plus the locked
Mathlib dependency. The development container is the supported setup; for local
requirements, inspect the canonical configuration and run `make doctor env`.
After changing shared configuration, run `make config` and `make config check`.

## Daily development workflow

Start from `main` on an isolated task branch. Run `make doctor env`, make a focused change, and build and check the affected book with `make books BOOK=<slug> check`. Run both `make test` and `make check all strict` before review so local validation matches the textbook-build CI standard. Make-based build files stay under the ignored `build/` directory, while LaTeX Workshop writes to the ignored `vscode-build/` directory. Release staging uses an automatically cleaned temporary directory.

## Cleaning outputs and caches

Run `make clean source` to remove disposable files that escape those output
directories, including LaTeX auxiliary files, `latexindent` logs, patch
backups/rejects, editor backups and swap files, and an interrupted manifest
write's temporary file. The command deliberately preserves `tree.txt`, build
output, formatter caches, Python caches, and Lean's `.lake` directory. These
artifact names are also excluded from Git and from `make tree` output.

Use `make clean build` to remove generated Make and VS Code build output. Local
tool caches are preserved unless explicitly selected with
`make clean cache {lake|tex|ruff|py|all}`. The `lake`, `tex`, and `ruff` scopes
remove their corresponding cache directories; `py` removes repository
`__pycache__` directories and `.pyc` files. Use `all` to remove every cache
category.

## Make command interface

Use Make targets as the public interface. `make help` is the authoritative command
and variable summary. Run `make report` for repository health and `make doctor
books [BOOK=<slug>]` for advisory textbook inspections.

Bulk builds use bounded concurrency; `BOOK_BUILD_JOBS` overrides the worker
limit. Use Make targets as the supported interface and call implementation
scripts directly only when debugging their specific output.

## Formatting

Use the Make targets rather than invoking formatters directly:

```sh
make format tex
make format py
make format sh
make format all
make format tex check
make format py check
make format sh check
make format all check
```

Without `check`, the selected formatter updates files in place. With `check`, it
only reports drift and exits unsuccessfully when a file needs formatting. Review
the resulting diff: formatting is mechanical and does not replace mathematical or
code review.

All formatter targets require their text files to end with exactly one LF.
`make format all` additionally applies that end-of-file rule to every non-empty,
Git-tracked text file; binary and untracked files are excluded. The complete
check applies the same repository-wide validation.

The LaTeX formatter is `latexindent`. It processes every Git-tracked `*.tex` and
`*.sty` file, including book sources, shared styles, and templates, with a
two-space default indentation setting and condenses consecutive blank lines to
one. Untracked drafts and other extensions are not included. Temporary
`latexindent` files are isolated and removed automatically. The command fails
with a dependency error when `latexindent` is not available.

For displays using `\by{...}`, follow the formatter-safe convention in the
[textbook writing guide](writing-guide.md#displayed-justifications-with-by). Review
formatter diffs because `latexindent` recognizes TeX structure heuristically.

Python formatting applies only to `scripts/` and `tests/`. Update mode applies
the configured safe Ruff fixes and formatting; check mode is non-mutating.
`pyproject.toml` owns formatter and lint policy, while
`.github/requirements-ci.txt` owns the Ruff version.

Shell formatting applies `shfmt` with the Bash language variant and two-space
indentation to `scripts/*.sh`. ShellCheck and `bash -n` remain the semantic and
syntax checks; formatting does not replace either check.

`make check source` deliberately runs no formatter or linter; it is the fast
structural and semantic gate and can run without a TeX installation or Ruff.
Source CI invokes Python, shell, and LaTeX formatting checks. The complete
`make check all [strict]` command includes all three gates before
checking proofs and building books. Use the focused
`make format {tex|py|sh|all} check` commands when a full build is unnecessary.

## Review

Review for scope, mathematical correctness, source rights, metadata ownership, and accidental generated files. Confirm every new chapter and section is included, labels use the book prefix, bibliography keys are unique, and frontmatter overrides exist only for substantive customization. Pull requests state affected books, validation commands, unresolved pre-existing warnings, and unavailable local-only assets.

## CI and publication

### Continuous integration

CI validates repository sources, formatting, tests, Lean proofs, affected PDFs,
and site output. Shared and ambiguous build inputs select every build-enabled
book; book-local changes select only their affected consumers. The workflow
definitions under `.github/workflows/` are authoritative for job structure,
permissions, concurrency, and publication implementation.

### Development PDF snapshots

Successful `main` builds maintain the development PDF snapshot used by Pages.
Maintainers can bootstrap or safely rebuild that snapshot by manually dispatching
**Build textbooks**, which selects every build-enabled book. Pull requests and
fork pull requests do not publish.

### Releases

Update the book's semantic `version` in `books.yml` and regenerate its metadata block, and run `make check all strict`. From a clean `main` workspace, run `make publish BOOK=<slug>`. The individual tag is `<slug>-v<version>` and must match the manifest version. Release happens only after the reviewed commit is merged and pushed. The local command fetches `origin/main`, requires exact equality with local `HEAD`, and never pushes source code. It requires `release: true`, builds and packages in a temporary directory with strict checks, creates and pushes an annotated tag, waits with a timeout for the corresponding successful Actions run, then uploads the locally built PDF and checksum without overwriting assets. CI does not build or attach release PDFs. The repository owner performs final publication, review, and merge.

## Contributor workflows

### Bug fixes and content writing

For a bug, reproduce it with the smallest relevant build or checker, correct only the owning file, add a regression test when tooling failed to detect it, then run the focused build and `make check all strict`. For content writing, work in one book and section, preserve notation and labels, verify sources and rights, build frequently, and avoid combining exposition with infrastructure changes.

### New contributors

Begin with the root README, [the contributing guide](CONTRIBUTING.md), and [the architecture guide](ARCHITECTURE.md). Choose a bounded issue, keep work on a task branch, use public Make commands, and ask before changing shared interfaces. `make doctor books BOOK=<slug>` offers advisory local diagnostics; it does not replace `make check all strict`.
