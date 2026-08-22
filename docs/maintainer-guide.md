# Maintainer guide

Use [the architecture guide](ARCHITECTURE.md) as policy and [design-decisions.md](design-decisions.md) for rationale.

## Reviewing changes

Confirm scope, ownership, mathematical correctness, provenance, labels, bibliography, generated files, and reported validation. AI-generated changes require the same review plus checks for invented citations, broad rewrites, unsupported claims, and changes that merely look plausible. Risk is highest in mathematical content, `common/styles/`, metadata/versioning, scripts, workflows, templates, and any repository-wide rename.

## Safe changes

For styles, identify every affected book, preserve macros, build all books, check logs, and visually review representative PDFs. For metadata, edit the owning source only, keep slug/version declarations unique, regenerate site pages when required, and validate release tags. For the shared image, keep the GHCR package public, never overwrite a release tag, and update the tag in the image workflow and every pinned consumer together. For scripts, preserve public commands, test failure paths, and keep diagnostics read-only unless mutation is explicit. For templates, scaffold or compile a representative book and keep local wrappers thin.

## Pull-request checklist

- Diff is focused; content and infrastructure are separated.
- No generated or local-only assets are tracked.
- Includes, labels, citations, metadata ownership, and rights are correct.
- `make check all strict` passed and broad shared changes received broad validation.
- Warnings and intentional limitations are stated.

## Release checklist

- Version and tag agree; the commit is approved, pushed to `main`, and local `HEAD` exactly matches `origin/main`.
- Release/site flags are intentional and changelog information is current.
- Source checks, builds, and log checks pass.
- The tag is annotated; artifacts and checksums have expected names; existing release assets remain untouched.

## Site publication checklist

- Set `build: true` and `site: true` in `books.yml` (`site: true` without a build is invalid).
- Metadata-only pages under `site/books/` are ignored build input generated from `books.yml`; do not edit or commit them.
- Run `make site check` for all site pages, or pass `BOOK=<slug>` when changing one book. Run `make site` only for a local Jekyll build, then run the relevant repository checks.
- Edit `site/assets/book.css` for book-page styling; Pages stages PDFs only for site-enabled books.

## Drift detection

Run `scripts/check-architecture.py`, `make report`, and the relevant `make doctor books BOOK=<slug>` inspection. Compare changes against architecture rather than historical accidents. Before changing common styles, scripts, or templates, document the motivation, test every consumer, preserve interfaces, and provide a rollback-sized diff.
