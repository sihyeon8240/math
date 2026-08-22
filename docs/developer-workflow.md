# Developer workflow

This guide describes ordinary repository operations. [the architecture guide](ARCHITECTURE.md) remains authoritative for structure and metadata ownership.

## Development

The publishing compiler is LuaLaTeX through `latexmk`, with TeX Live 2026 as the official toolchain. Formal proofs use the Lean version pinned in `lean/lean-toolchain` and the locked Mathlib dependency. For a local setup, install those tools with `elan`, plus Python 3, GNU Make, Bash, ripgrep, Ghostscript, and `tree`. Install the pinned Python tooling with `python3 -m pip install --requirement .github/requirements-ci.txt`. VS Code users may instead reopen the repository in its development container, which uses the same immutable build image as PDF CI. Run `make doctor env` to verify either environment.

Start from `main` on an isolated task branch. Run `make doctor env`, make a focused change, and build the affected book with `make books BOOK=<slug>`. Run both `make test` and `make check all strict` before review so local validation matches the textbook-build CI standard. Make-based build files stay under the ignored `build/` directory, while LaTeX Workshop writes to the ignored `vscode-build/` directory. Release staging uses an automatically cleaned temporary directory.

Use Make targets as the public interface. Run `make help` for a concise command and variable summary; the common entry points include `make format {tex|py|all} [check]`, `make test`, `make check manifest`, `make check source`, `make books BOOK=<slug>`, `make books`, `make check all`, `make check all strict`, `make site`, and `make site check`. Formatting without `check` updates the selected sources; check mode is non-mutating and is enforced by source CI. Run `make report` for an informational health report. Use `make doctor books` for advisory inspections of every registered textbook, or pass `BOOK=<slug>` to inspect one.

Bulk builds run enabled books in a bounded worker pool and report every failed slug after all targets finish. Set `BOOK_BUILD_JOBS` to a positive integer to cap concurrency, for example `BOOK_BUILD_JOBS=2 make books`; an invalid or explicitly empty value is an error. Without an override, the runner uses the detected CPU count capped at four, falling back to two when detection is unavailable. When a book finishes, its captured console output is printed as one block and the freed slot starts the next book, while persistent LaTeX output remains under `build/<slug>/`.

Do not normally call `build-book.sh`, `build-all.sh`, `check.sh`, `books.py add`, or `generate-site-pages.py` directly. They are implementation layers used by Make targets and automation. Maintainers may call read-only query/check commands such as `scripts/books.py list`, `scripts/books.py version`, `scripts/check-architecture.py`, and `scripts/check-log.py` when debugging their specific output.

## Formatting

Use the Make targets rather than invoking formatters directly:

```sh
make format tex
make format py
make format all
make format tex check
make format py check
make format all check
```

Without `check`, the selected formatter updates files in place. With `check`, it
only reports drift and exits unsuccessfully when a file needs formatting. Review
the resulting diff: formatting is mechanical and does not replace mathematical or
code review.

The LaTeX formatter is `latexindent`. It processes every Git-tracked `*.tex` and
`*.sty` file, including book sources, shared styles, and templates, with a
two-space default indentation setting. Untracked drafts and other extensions are
not included. Temporary `latexindent` files are isolated and removed
automatically. The command fails with a dependency error when `latexindent` is
not available.

`latexindent` recognizes TeX structure heuristically rather than expanding
repository macros. In particular, dollar-delimited math inside `\by{...}` can
cause it to split a surrounding display incorrectly and miss `array` indentation
or trailing `\\` alignment. Follow the `\by` convention in the
[textbook writing guide](writing-guide.md#shared-mathematics-commands): use
`\ensuremath{...}` for every mathematical portion of the argument. A successful
format check does not prove that an unrecognized block follows the visual
alignment convention, so review formatter diffs when editing such displays.

Python formatting applies only to `scripts/` and `tests/`. Update mode first runs
Ruff safe lint fixes and import sorting, then formats the files. Check mode runs
both `ruff format --check` and the non-mutating Ruff lint check. The repository
configuration in `pyproject.toml` targets Python 3.12, uses an 88-character line
length, and enables the selected error, Pyflakes, and import-sorting rule groups.
The Ruff version is pinned in `.github/requirements-ci.txt`.

`make check source` deliberately runs no formatter or linter; it is the fast
structural and semantic gate and can run without a TeX installation or Ruff.
Source CI invokes Python formatting and lint and LaTeX formatting as separate
steps. The complete `make check all [strict]` command includes both gates before
checking proofs and building books. Use the focused
`make format {tex|py|all} check` commands when a full build is unnecessary.

## Review

Review for scope, mathematical correctness, source rights, metadata ownership, and accidental generated files. Confirm every new chapter and section is included, labels use the book prefix, bibliography keys are unique, and frontmatter remains a thin customization wrapper. Pull requests state affected books, validation commands, unresolved pre-existing warnings, and unavailable local-only assets.

## CI

The development container and GitHub Actions textbook builds, including strict pull-request builds, use the same immutable image pinned in `.devcontainer/devcontainer.json` and `.github/workflows/build.yml`; repository checks require those references to match. Official release PDFs are built locally as described below; the tag workflow does not compile them. The image is built from `.devcontainer/Dockerfile`; `scripts/check-toolchain.sh` is copied into the image and verifies its installed commands, Python dependency, and TeX packages during the build and a smoke test. The repository-level `scripts/check-environment.sh` calls that toolchain check before validating the checked-out repository, and is used by `make doctor env` and the development container's post-create command without becoming an image input.

The image tag is immutable and the GHCR package must remain public so local Dev Containers can pull it without credentials. To update the Dockerfile or toolchain check, choose a new date-versioned `RELEASE_TAG`, publish it by dispatching `build-image.yml` from the task branch, verify that the package is public, then run `make image-pin DIGEST=<64-character-sha256>` to update every pinned image reference before merge. A later main-branch run detects the existing immutable tag and does not overwrite it. `scripts/check-image-tag.sh` distinguishes Dockerfile/toolchain-check changes from repository-environment or workflow-only maintenance: an existing tag fails only when an actual image input changed, while workflow-only pushes and manual dispatches succeed without overwriting it. Never store a registry token in the repository.

Third-party GitHub Actions are pinned to reviewed commit SHAs, with their corresponding major versions recorded in comments. Dependabot proposes updates through the existing configuration; review both the resolved commit and the major-version comment when accepting an update.


The repository source-check script validates the manifest, site-page rendering, architecture, assembly targets, generated README details, orphan files, metadata declarations, bibliography integrity, label policy, template wrappers, Python syntax, image-pin consistency, and tracked generated files. Python formatting and lint and LaTeX formatting run as separate source-CI steps. README title and descriptive metadata drift is advisory; generated README drift is an error. On pushes and pull requests, `scripts/affected-books.py` selects changed book-local inputs and consumers of changed shared TeX dependencies; ambiguous build inputs fall back to all `build: true` books. The matrix compiles only that set through LuaLaTeX/`latexmk` and applies the strict log check, so no second all-book strict build runs. Extend the existing repository checker for new source rules; do not edit workflows merely to add one.

### Development PDF publication

Only the single publish job on a successful `main` build has `contents: write`. It downloads the affected matrix artifacts, checks out (or initializes) `generated-pdfs`, replaces only those `pdf/<slug>.pdf` files, verifies every `site: true` PDF exists, and pushes one ordinary commit. The branch stores the covered source commit in `.source-sha`. Each main run computes its matrix from that commit rather than only the immediately preceding push, so replacement of a pending concurrency run cannot omit an intermediate change. A publish step re-fetches `main` and exits without writing if its source is stale; serialized publishers therefore cannot overwrite a newer snapshot. PRs and fork PRs cannot publish. Ordinary commits were chosen instead of force-pushed one-commit history to remain compatible with branch protection and avoid destructive recovery semantics. Binary history can be pruned later as an explicit maintenance operation if repository size warrants it.

The first snapshot is bootstrapped by manually dispatching **Build textbooks**. Manual dispatch deliberately selects every `build: true` book, so the publish job can create `generated-pdfs` and verify the complete site set. Pages manual dispatch requires that branch to exist. Later site-only pushes create an empty PDF matrix, advance the snapshot source marker, and deploy Pages with the existing validated PDFs. Pages is invoked only when the planner reports a site change or at least one PDF was rebuilt; documentation-only and other Pages-irrelevant changes do not invoke it. The snapshot keeps only current `site: true` PDFs. Delete `.source-sha` or manually dispatch Build textbooks on `main` to force a safe full rebuild; the latter is also the initial bootstrap procedure.

## Releases

Update the book's single semantic `\version` in `metadata.tex` and run `make check all strict`. From a clean `main` workspace, run `make publish BOOK=<slug>`. The individual tag is `<slug>-v<version>` and must match metadata. Release happens only after the reviewed commit is merged and pushed. The local command fetches `origin/main`, requires exact equality with local `HEAD`, and never pushes source code. It requires `release: true`, builds and packages in a temporary directory with strict checks, creates and pushes an annotated tag, waits with a timeout for the corresponding successful Actions run, then uploads the locally built PDF and checksum without overwriting assets. CI does not build or attach release PDFs. The repository owner performs final publication, review, and merge.

## Bug fixes and content writing

For a bug, reproduce it with the smallest relevant build or checker, correct only the owning file, add a regression test when tooling failed to detect it, then run the focused build and `make check all strict`. For content writing, work in one book and section, preserve notation and labels, verify sources and rights, build frequently, and avoid combining exposition with infrastructure changes.

## New contributors

Begin with the root README, [the contributing guide](CONTRIBUTING.md), and [the architecture guide](ARCHITECTURE.md). Choose a bounded issue, keep work on a task branch, use public Make commands, and ask before changing shared interfaces. `make doctor books BOOK=<slug>` offers advisory local diagnostics; it does not replace `make check all strict`.
