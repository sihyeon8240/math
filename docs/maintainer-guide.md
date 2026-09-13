# Maintainer guide

Use [the architecture guide](ARCHITECTURE.md) as policy and [design-decisions.md](design-decisions.md) for rationale.

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

- Version and tag agree; the change is reviewed and merged into remote `main`
  through a pull request, and local `HEAD` exactly matches `origin/main`.
- Release and site flags are intentional.
- Source checks, builds, and log checks pass.
- The tag is annotated; artifacts and checksums have expected names; existing release assets remain untouched.
- `make publish` has staged a draft. Download and review its PDF and verify the
  checksum before manually publishing it; follow the
  [recovery procedure](developer-workflow.md#recovering-an-interrupted-release)
  if preparation was interrupted.

## Site publication checklist

Follow [Site metadata](site-metadata.md) for publication flags, generation,
validation, and styling. Confirm that generated pages remain untracked.

## Drift detection

Run `scripts/check-architecture.py`, `make report`, and the relevant `make doctor books BOOK=<slug>` inspection. Compare changes against architecture rather than historical accidents. Before changing common styles, scripts, or templates, document the motivation, test every consumer, preserve interfaces, and provide a rollback-sized diff.

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
