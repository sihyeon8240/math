# Developer workflow

This guide describes ordinary repository operations. [The architecture guide](ARCHITECTURE.md) remains authoritative for structure and metadata ownership.

## Development environment

The publishing compiler is LuaLaTeX through `latexmk`. Tool versions are owned by
`config/toolchain.env`. The reviewed local and devcontainer image pin lives in
`config/container-image.txt`; CI prepares an image from canonical build inputs
and passes its tested immutable digest to downstream jobs. Lean consumes the
synchronized `lean/lean-toolchain` and the locked Mathlib dependency. The development container is the supported setup; for local
requirements, inspect the canonical configuration and run `make doctor env`.
After changing shared configuration, run `make config` and `make config check`.

## Daily development workflow

Keep local `main` synchronized with `origin/main` using fast-forward updates.
Never commit or push directly to `main`; remote changes enter through pull
requests. Create `local-work` from the synchronized `main` and accumulate
focused, independently revertible commits there. Sequential requests may share
this branch and one manageable batch PR. Separate large or risky changes, or
changes likely to be deferred independently, into their own branches and PRs.

Validate the combined batch before review. The repository owner reviews and
merges the PR after the required GitHub Actions checks pass. After the merge,
fast-forward local `main` to `origin/main` and recreate `local-work` from it for
the next batch. Before removing the old branch, confirm that all work was
included in the merge or preserved elsewhere. Start with fresh branch history
after a squash merge to avoid carrying already merged commits into the next PR.

Run `make doctor env`, make focused changes, and build and check the affected book with `make books BOOK=<slug> check`. Select the required checks from [Contributing](CONTRIBUTING.md#validation-by-change-category) before review. Make-based build files stay under the ignored `build/` directory, while LaTeX Workshop writes to the ignored `vscode-build/` directory. Release packages are retained as GitHub Actions artifacts.

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

Review formatter diffs because `latexindent` recognizes TeX structure
heuristically.

Python formatting applies only to `scripts/` and `tests/`. Update mode applies
the configured safe Ruff fixes and formatting; check mode is non-mutating.
`pyproject.toml` owns formatter and lint policy, while
`config/toolchain.env` owns the Ruff version synchronized into
`.github/requirements-ci.txt` by `make config`.

Shell formatting applies `shfmt` with the Bash language variant and two-space
indentation to `scripts/*.sh`. ShellCheck and `bash -n` remain the semantic and
syntax checks; formatting does not replace either check.

`make check source` runs structural checks, documentation checks, `bash -n`,
and ShellCheck at error severity. It requires ShellCheck and ripgrep, but runs
no formatter and needs neither a TeX installation nor Ruff.
`make check docs` checks local Markdown links and heading anchors plus the
documented theorem-environment list against the shared style, without network
access or TeX. It does not verify prose claims or external URLs.
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

`build.yml` owns PR and main CI, including the existing **Check sources** and
**Verify textbook builds** status checks. Source checks and affected-book planning
start independently; image preparation runs once and its immutable digest is
shared by formatting and PDF jobs. Both events still validate sources and Lean.

Cache restores still run normal validation. After a merge, CI may reuse a
verified PR artifact when its full source tree and build environment match;
otherwise it builds the affected PDF normally. See the
[maintainer guide](maintainer-guide.md#ci-caches-and-verified-pdf-reuse) for cache
boundaries, artifact eligibility, and rebuild procedures.

### Development PDF snapshots

Successful `main` builds maintain the development PDF snapshot used by Pages.
Maintainers can bootstrap or safely rebuild that snapshot by manually dispatching
**Build textbooks**, which selects every build-enabled book. Pull requests and
fork pull requests do not publish.

### Releases

A reviewed `release: false` to `release: true` change requests publication of
that book's current version, so a first release can use `0.1.0` unchanged. A newly
registered book with `release: true` also requests its first publication. While
`release: true` remains set, only a version increase requests another release;
ordinary content changes do not. Version changes must increase in semantic-version
order. Release targets must also have `build: true`. A version change while
`release: false` does not publish. All books initially have `release: false`.

On `local-work` or another development branch, run:

```bash
make release-prepare BOOK=mathematical-analysis-1 VERSION=0.1.0
```

This enables `release: true`, sets that book's version in `books.yml`, and
synchronizes its generated assembly, equivalent to `make contents all BOOK=<slug>`.
The current version is accepted when enabling a disabled book; an already enabled
book requires a higher version (for example `VERSION=0.2.0`). It preserves unrelated
manifest formatting and edits. It does not commit, push, create a PR, build a PDF,
or create a tag. Direct preparation on `main` or detached HEAD is rejected.
Review and commit the resulting changes with the textbook work, complete the
applicable checks in [Contributing](CONTRIBUTING.md#validation-by-change-category),
and submit the usual batch PR. Merging the release preparation authorizes automatic
public release; no second approval is required. The old `make publish` interface
has been removed.

For publication artifacts, tags, and failure recovery, see the
[maintainer publication procedures](maintainer-guide.md#release-publication).
