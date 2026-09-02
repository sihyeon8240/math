# Design decisions

This records why established choices fit this repository; [the architecture guide](ARCHITECTURE.md) defines the choices themselves. None is claimed to be universally optimal.

## Content boundaries

### Independent textbooks and unshared mathematics

- **Decision:** each book owns all exposition.
- **Motivation:** readers and releases must stand alone.
- **Benefits:** clear provenance, local revision, and no hidden coupling.
- **Tradeoff:** repeated explanations can drift.
- **Future direction:** improve diagnostics, not cross-book includes.

### Shared infrastructure

- **Decision:** styles, templates, and automation are common.
- **Motivation:** publishing mechanics are genuinely repository-wide.
- **Benefits:** consistent output and fewer fixes.
- **Tradeoff:** a shared change has a broad blast radius.
- **Future direction:** validate every book after common changes.

## Assembly and metadata

### Manifest-owned metadata

- **Decision:** `books.yml` owns repository and publication metadata; generated
  TeX and site projections consume that single record.
- **Motivation:** release, site, and TeX consumers should agree without parsing prose.
- **Benefits:** one automation registry and no duplicated metadata.
- **Tradeoff:** generated projections must be regenerated and checked for drift.
- **Future direction:** add fields only for real consumers and preserve strict checks.

### Declarative book contents

- **Decision:** each book's `chapters.yml` orders chapters and each chapter's `sections.yml` orders logical sections; generated complete `book.tex` files and `index.tex` files provide literal LaTeX assembly.
- **Benefits:** titles and order have one machine-readable source, while committed generated assembly remains inspectable.
- **Tradeoff:** contributors must regenerate after manifest edits.
- **Future direction:** extend the schema only when a real cross-consumer need appears.

### Optional appendices

- **Decision:** books opt in.
- **Benefits:** structure follows subject needs.
- **Tradeoff:** automation must tolerate both shapes.
- **Future direction:** retain lightweight detection.

### Metadata-only site pages

- **Decision:** site detail pages are generated only from `books.yml` and contain no separately maintained description.
- **Benefits:** no descriptive drift or hidden README automation contract.
- **Tradeoff:** the PDF and source remain the authoritative subject detail.
- **Future direction:** keep site metadata manifest-owned.

## Publishing and site generation

### Ephemeral release staging

- **Decision:** development builds remain under ignored `build/`; release packaging uses an automatically cleaned temporary directory.
- **Benefits:** no persistent staging state and a narrower public interface.
- **Tradeoff:** local release artifacts exist only on GitHub after upload.
- **Future direction:** preserve asset immutability.

### Ephemeral manifest-derived site pages

- **Decision:** site metadata is generated into ignored book-page front matter immediately before Jekyll runs; there is no committed page or separate Jekyll data copy.
- **Benefits:** source-only diffs and one canonical registry.
- **Tradeoff:** local Jekyll builds require a generation step.
- **Future direction:** retain non-mutating render checks.

## Customization and shared infrastructure

### Optional local overrides

- **Decision:** books use shared frontmatter and styles directly unless a substantive local override file exists.
- **Benefits:** no empty placeholders or pass-through wrappers, while customization remains available.
- **Tradeoff:** optional-file loading is part of the stable `book.tex` template.
- **Future direction:** create overrides only when a book actually differs.

## Build and validation architecture

### Thin build scripts

- **Decision:** scripts compose manifest queries, `latexmk`, and log checks.
- **Benefits:** understandable failures and replaceable layers.
- **Tradeoff:** several small entry points.
- **Future direction:** keep Make targets as the contributor interface.

### Layered validation

- **Decision:** manifest, source, label, build, and log checks remain separate.
- **Benefits:** focused diagnostics and cheap early failures.
- **Tradeoff:** overlap and more commands.
- **Future direction:** improve messages rather than merge layers.

## Repository-wide conventions

### Book-prefixed labels

- **Decision:** `nt:`, `la:`, and `an:` prevent repository-global collisions.
- **Benefits:** unambiguous references.
- **Tradeoff:** longer labels and legacy migration.
- **Future direction:** migrate only in coordinated, verified changes.

### Documented policies

- **Decision:** stable contracts are written down.
- **Benefits:** consistent human and AI work.
- **Tradeoff:** documents need maintenance.
- **Future direction:** cross-reference instead of copying policy text.
