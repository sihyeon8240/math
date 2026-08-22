# Design decisions

This records why established choices fit this repository; [the architecture guide](ARCHITECTURE.md) defines the choices themselves. None is claimed to be universally optimal.

## Content boundaries

- **Independent textbooks and unshared mathematics.** Decision: each book owns all exposition. Motivation: readers and releases must stand alone. Benefits: clear provenance, local revision, and no hidden coupling. Tradeoff: repeated explanations can drift. Future: improve diagnostics, not cross-book includes.
- **Shared infrastructure.** Decision: styles, templates, and automation are common. Motivation: publishing mechanics are genuinely repository-wide. Benefits: consistent output and fewer fixes. Tradeoff: a shared change has a broad blast radius. Future: validate every book after common changes.

## Assembly and metadata

- **`metadata.tex` remains.** Decision: retain LaTeX-facing title, course, slug, version, and PDF fields. Motivation: TeX and release tooling need book-local values. Benefits: readable builds and no generation step. Tradeoff: some title concepts overlap the manifest. Future: warnings may improve; ownership should not move.
- **`books.yml` is repository metadata.** Decision: status, order, and participation flags are canonical there. Benefits: one automation registry. Tradeoff: presentational titles also exist in TeX. Future: preserve advisory consistency checks.
- **Chapter `index.tex` and explicit `book.tex` lists.** Decision: chapter indices order sections and the entry point orders chapters. Benefits: assembly is inspectable and diffs are meaningful. Tradeoff: manual includes can be missed. Future: validators should diagnose mistakes; generation would reduce transparency.
- **Optional appendices.** Decision: books opt in. Benefits: structure follows subject needs. Tradeoff: automation must tolerate both shapes. Future: retain lightweight detection.
- **Metadata-only site pages.** Decision: site detail pages are generated only from `books.yml` and contain no separately maintained description. Benefits: no descriptive drift or hidden README automation contract. Tradeoff: the PDF and source remain the authoritative subject detail. Future: keep site metadata manifest-owned.

## Publishing operations

- **Ephemeral release staging.** Decision: development builds remain under ignored `build/`; release packaging uses an automatically cleaned temporary directory. Benefits: no persistent staging state and a narrower public interface. Tradeoff: local release artifacts exist only on GitHub after upload. Future: preserve asset immutability.
- **Ephemeral manifest-derived site pages.** Decision: site metadata is generated into ignored book-page front matter immediately before Jekyll runs; there is no committed page or separate Jekyll data copy. Benefits: source-only diffs and one canonical registry. Tradeoff: local Jekyll builds require a generation step. Future: retain non-mutating render checks.
- **Retained template wrappers.** Decision: books include common frontmatter through local thin files. Benefits: stable book assembly and an override point. Tradeoff: an extra indirection. Future: drift detection should remain advisory until structure breaks.
- **Thin build scripts.** Decision: scripts compose manifest queries, `latexmk`, and log checks. Benefits: understandable failures and replaceable layers. Tradeoff: several small entry points. Future: keep Make targets as the contributor interface.
- **Layered validation.** Decision: manifest, source, label, build, and log checks remain separate. Benefits: focused diagnostics and cheap early failures. Tradeoff: overlap and more commands. Future: improve messages rather than merge layers.
- **Book-prefixed labels.** Decision: `nt:`, `la:`, and `an:` prevent repository-global collisions. Benefits: unambiguous references. Tradeoff: longer labels and legacy migration. Future: migrate only in coordinated, verified changes.
- **Documented policies.** Decision: stable contracts are written down. Benefits: consistent human and AI work. Tradeoff: documents need maintenance. Future: cross-reference instead of copying policy text.
