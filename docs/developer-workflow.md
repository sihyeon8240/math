# Developer workflow

This guide describes ordinary repository operations. [the architecture guide](ARCHITECTURE.md) remains authoritative for structure and metadata ownership.

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

Run `make doctor env`, make focused changes, and build and check the affected book with `make books BOOK=<slug> check`. Select the required checks from [Contributing](CONTRIBUTING.md#validation-by-change-category) before review. Make-based build files stay under the ignored `build/` directory, while LaTeX Workshop writes to the ignored `vscode-build/` directory. Release staging uses an automatically cleaned temporary directory.

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

Lean caches `.lake` by OS, architecture, toolchain, dependency lock, Lake
configuration, and Lean sources. LaTeX caches each book's `build/<slug>/` by OS,
architecture, image digest, and source tree, with fallback only within the same
book and image. Cache hits still run the normal build and strict checks. GitHub
cache scope means PR caches are generally unavailable to main; main warms its
own caches, which subsequent PRs can restore.

After a merge, each affected PDF job first looks for a successful `build.yml`
PR run for the merged PR's head in this repository. Reuse requires an identical
full Git tree (including workflows and build settings), image index digest,
platform, validation policy, run ID/attempt, and PDF/log checksums. The downloaded
archive must also match GitHub's artifact digest, and its log is strictly checked
again. A match skips the TeX container build and republishes the verified PDF as
the current run's artifact for the existing snapshot pipeline.

Verified artifacts expire after 14 days. Missing, expired, mismatched, fork,
failed-run, or unavailable artifacts fall back to a normal cached build. Lookup
is bounded to 30 matching successful runs and 100 artifacts per run. Full-tree
matching is deliberately conservative: even an unrelated change after PR
validation can cause a rebuild. Merge, squash, and rebase do not need identical
commit SHAs when their final source trees match. A manual **Build textbooks**
dispatch skips PR reuse and builds every enabled book. Bump the cache versions
or `strict-pdf-v1` policy when their corresponding semantics change.

### Development PDF snapshots

Successful `main` builds maintain the development PDF snapshot used by Pages.
Maintainers can bootstrap or safely rebuild that snapshot by manually dispatching
**Build textbooks**, which selects every build-enabled book. Pull requests and
fork pull requests do not publish.

### Releases

Update the book's semantic `version` in `books.yml`, run
`make contents chap BOOK=<slug>`, and complete the applicable validation in
[Contributing](CONTRIBUTING.md#validation-by-change-category). Merge the reviewed
change into remote `main` through a pull request before preparing a release.

From a clean `main` workspace, run `make publish BOOK=<slug>`. The command requires
`release: true`, fetches `origin/main`, and requires exact equality with local
`HEAD`. It builds under `build/<slug>/`, strictly checks the log, and packages the
PDF and `SHA256SUMS` in an automatically cleaned temporary directory. It creates
and pushes the annotated `<slug>-v<version>` tag; it never pushes source code.

The command waits for the successful release workflow, which validates the tag
and creates a draft GitHub Release. CI does not build or attach release PDFs.
The local command uploads the PDF and checksum without overwriting existing
assets and leaves the release as a draft. It refuses asset changes to an already
public release. The repository owner downloads and reviews the staged PDF,
checks `SHA256SUMS`, and then publishes the draft through GitHub. Preparing assets
and making them public are separate steps.

#### Recovering an interrupted release

- If tag push failed, inspect the local and remote tag before retrying. An
  existing local tag must be annotated and point to the release commit; never
  move an existing publication tag to a different commit.
- If workflow discovery timed out, check the tag's **Release textbooks** run on
  GitHub. If that run failed, resolve the cause and rerun it. Pushing an unchanged
  tag again does not create a new push event. Wait for a successful run before
  retrying the local command.
- If asset upload was interrupted and `main` still points to the release commit,
  rerun `make publish BOOK=<slug>`. Identical existing assets are retained and
  missing assets are uploaded. A byte mismatch is an error, even when the PDF was
  rebuilt from the same source; do not delete or overwrite assets to hide it.
- If `main` has advanced, do not reset it or move the tag to satisfy the command.
  Use a separate checkout of the tagged commit to inspect or rebuild the PDF and
  verify it against any uploaded checksum. A maintainer may resume the missing
  asset upload with `scripts/upload-release-assets.sh <tag> <pdf> <checksums>`
  after confirming the release is still a draft and its validation run passed.
  If the original bytes cannot be recovered consistently, leave the draft
  unpublished and prepare a reviewed new version.

Temporary packaging files are removed on failure as well as success. The build
PDF remains under `build/<slug>/` until the next build or cleanup; preserve it
when investigating an interrupted upload.

## Contributor workflows

### Bug fixes and content writing

For a bug, reproduce it with the smallest relevant build or checker, correct only the owning file, add a regression test when tooling failed to detect it, then run the checks required by [Contributing](CONTRIBUTING.md#validation-by-change-category). For content writing, work in one book and section, preserve notation and labels, verify sources and rights, build frequently, and avoid combining exposition with infrastructure changes.

### New contributors

Begin with the root README, [the contributing guide](CONTRIBUTING.md), and [the architecture guide](ARCHITECTURE.md). Choose a bounded issue, follow the batch workflow above (or use a separate task branch when isolation is useful), use public Make commands, and ask before changing shared interfaces. `make doctor books BOOK=<slug>` offers advisory local diagnostics; it does not replace the required validation in [Contributing](CONTRIBUTING.md#validation-by-change-category).
