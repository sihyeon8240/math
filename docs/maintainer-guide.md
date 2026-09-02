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

- Diff is focused; content and infrastructure are separated.
- No generated or local-only assets are tracked.
- Includes, labels, citations, metadata ownership, and rights are correct.
- `make check all strict` passed and broad shared changes received broad validation.
- Warnings and intentional limitations are stated.

## Release checklist

- Version and tag agree; the commit is approved, pushed to `main`, and local `HEAD` exactly matches `origin/main`.
- Release and site flags are intentional.
- Source checks, builds, and log checks pass.
- The tag is annotated; artifacts and checksums have expected names; existing release assets remain untouched.

## Site publication checklist

Follow [Site metadata](site-metadata.md) for publication flags, generation,
validation, and styling. Confirm that generated pages remain untracked.

## Drift detection

Run `scripts/check-architecture.py`, `make report`, and the relevant `make doctor books BOOK=<slug>` inspection. Compare changes against architecture rather than historical accidents. Before changing common styles, scripts, or templates, document the motivation, test every consumer, preserve interfaces, and provide a rollback-sized diff.
