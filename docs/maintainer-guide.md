# Maintainer guide

Use [the architecture guide](ARCHITECTURE.md) for repository structure and
ownership, and the [documentation map](README.md) to find task-specific policies.

## Reviewing changes

Confirm scope, ownership, mathematical correctness, provenance, labels, bibliography, generated files, and reported validation. AI-generated changes require the same review plus checks for invented citations, broad rewrites, unsupported claims, and changes that merely look plausible. Risk is highest in mathematical content, `common/styles/`, metadata/versioning, scripts, workflows, templates, and any repository-wide rename.

## Safe changes

For shared styles, metadata, images, scripts, and templates, follow the owning
policy and validation scope in the [architecture guide](ARCHITECTURE.md) and the
operational commands in the [developer workflow](developer-workflow.md). Preserve
public interfaces and test every affected consumer.

## Pull-request checklist

- The batch is manageable to review; unrelated changes use separate commits,
  large or risky changes use separate PRs, and parts needed for one coherent
  result stay together.
- Generated files follow the [storage and tracking policy](ARCHITECTURE.md#generated-files-and-local-outputs); no build artifacts or local-only assets are added.
- Includes, labels, citations, metadata ownership, and rights are correct.
- The checks required by [Contributing](CONTRIBUTING.md#validation-by-change-category) passed; unavailable checks are explained.
- Warnings and intentional limitations are stated.

## Release checklist

- Prepare the first or an increasing version on a development branch with
  `make release-prepare BOOK=<slug> VERSION=<version>` and review its generated
  assembly changes in the normal PR.
- Confirm `build: true`. Enabling `release: true` requests first publication;
  subsequent releases require a version increase.
- Review the PR PDF before merging. Merging the release preparation authorizes
  automatic publication after main CI succeeds.
- Confirm the public release contains the versioned PDF and `SHA256SUMS`, and
  that its annotated tag points to the validated main commit.
- Preserve existing tags and assets. Recover failures through the original
  workflow's failed jobs using the
  [recovery procedure](#recovering-an-interrupted-release).

## Release publication

`build.yml` compares the PR base or the main push's `before` commit with the
checked-out manifest, independently of the development snapshot baseline.
Release books are included in the PDF build matrix even if the snapshot has
already advanced. PRs validate the plan without publishing. Ordinary manual
**Build textbooks** runs refresh development PDFs only.

After the main source, Lean, formatting, and strict PDF gates pass, `build.yml`
calls `release.yml` with the release book matrix. The build jobs package the
strictly checked PDFs and `SHA256SUMS` into `<slug>-release` artifacts retained
for 90 days. The publication jobs use those same-run packages and tag the exact
validated `GITHUB_SHA`, even when `main` has since advanced. They never use the
mutable `generated-pdfs` snapshot as a release source. Pages deployment and
versioned releases are independent consumers of the validated build.

Each publication creates an annotated `<slug>-v<version>` tag, stages a draft,
uploads `<slug>-v<version>.pdf` and `SHA256SUMS`, downloads and verifies both, then
automatically publishes the draft. Versions with a prerelease suffix are marked
as prereleases. Releases use their book tag as the title; GitHub-generated notes
are repository-wide. No book claims the repository-wide `Latest` designation.
The release process does not change the descriptive book `status` in `books.yml`.
Only publication jobs receive repository-content write permission for releases.
Tag pushes no longer trigger a separate release workflow.

### Recovering an interrupted release

- Use **Re-run failed jobs** on the original main **Build textbooks** run. Its
  original event, commit, plan, and retained package identify the release even
  after `main` advances. Do not dispatch a new build to recover an old version.
- If publication failed after packaging, retain the original `<slug>-release`
  artifact. Avoid rerunning successful build jobs: a rebuilt PDF can differ in
  bytes, and an existing immutable artifact must not be replaced.
- Re-enabling a previously published book does not reset its release history.
  Choose a higher version if its current version already has a tag; the existing
  tag conflict guard still applies.
- An existing tag must be annotated and point to the same validated commit.
  Existing draft assets must match the original package byte for byte; only
  missing assets are uploaded. Conflicts stop publication without overwriting.
- An already-public release is left unchanged on retry. If publication succeeded
  just before the job lost its connection, a retry therefore completes safely.
- If a retained package has expired or conflicting bytes cannot be recovered,
  leave the draft unpublished and prepare a reviewed higher version. Never move
  an existing tag or overwrite public assets to force recovery.
- Concurrent runs are isolated by book and source commit. A later main commit
  does not suppress an earlier version's publication. Main push runs have separate
  concurrency groups per commit; development snapshot writes remain serialized.
  If a run is cancelled or
  fails, recover that original run explicitly; later pushes do not implicitly
  backfill missed versions.

## Site publication checklist

Follow [Site metadata](site-metadata.md) for publication flags, generation,
validation, and styling. Confirm that generated pages remain untracked.

## Drift detection

Run `make check source` for structural validation, `make report` for repository
health, and `make doctor books BOOK=<slug>` for advisory textbook inspections. Compare changes against architecture rather than historical accidents. Before changing common styles, scripts, or templates, document the motivation, test every consumer, preserve interfaces, and provide a rollback-sized diff.

## CI caches and verified PDF reuse

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

## Toolchain image operations

### Multi-platform toolchain images

`prepare-image.yml` builds `linux/amd64` on `ubuntu-24.04` and `linux/arm64`
on `ubuntu-24.04-arm`. Both native runners must be available to the repository.
Each runner loads its single-platform image, checks its architecture, runs the
toolchain smoke test, and pushes the tested image under a run-specific tag.
The publish job combines the recorded immutable digests only after both builds
succeed. Consumers pin the resulting multi-platform index digest, allowing
Docker to select the host architecture.

The content tag hashes the Dockerfile, toolchain configuration, toolchain check,
platform list, and build policy version. Bump the policy version when changing
build or validation semantics that require a fresh image. Existing tags are
reused only if their index includes both Linux platforms; incompatible existing
tags fail without being overwritten. Publication validates the index by digest
before returning it to callers. The first successful workflow run updates the
consumer pin through the existing pin pull request automation.

Digest artifacts expire after one day. Temporary `build-<run>-<attempt>-<arch>`
registry tags are retained, including when the other architecture fails; final
image tags are published only after both smoke tests pass. No QEMU or new
Python dependencies are required. See the [Docker multi-platform CI guide](https://docs.docker.com/build/ci/github-actions/multi-platform/).
