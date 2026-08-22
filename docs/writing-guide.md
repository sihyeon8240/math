# Textbook writing guide

This guide describes the repository's supported authoring interface. It is a
review checklist, not a requirement to print the same headings in every section.

## Creating and assembling a book

Create and register a book from the repository root with:

```sh
make new-book SLUG=<slug> TITLE="<title>"
```

The script copies `common/templates/`, creates the first chapter and section,
and registers the book in `books.yml`. The lower-level `books.py add` command
only registers an existing directory.

Each `books/<slug>/book.tex` is the LaTeX entry point and owns document-wide
setup and the ordered `\include` list. Each chapter directory has an `index.tex`
that declares the chapter and inputs or includes its section files in reading
order.

Name a single-file logical section `NN-section-name.tex`. If it must be split,
keep the same logical number and slug in every source and add consecutive
suffixes beginning with `-a`, for example `02-main-result-a.tex` and
`02-main-result-b.tex`. Put split parts next to each other in suffix order in
`index.tex`; do not use context-dependent names such as `section-part-2`. See
the canonical naming policy in [the architecture guide](ARCHITECTURE.md#naming-conventions).

Write those assembly edges literally as `\include{chapters/01-name/index}` or `\input{01-section}` (a `.tex` suffix is also allowed). Do not generate paths with macros, loops, conditionals, `\csname`, filesystem discovery, or generated lists, and delete obsolete includes rather than commenting them out. The static assembly contract and its rationale are authoritative in [the architecture guide](ARCHITECTURE.md#static-assembly-syntax-contract); the architecture checker depends on it to find ordering errors and orphan files.

A section file declares one section and contains its body. Use standard
`\chapter{Chapter Title}` and `\section{Section Title}` declarations. Do not use
chapter or section as environments. Existing legacy wrappers are migrated only
after output regression checks. Section files do not load packages directly;
`book.tex` loads the shared `textbook` package and book-local `local-style`
extensions.

Files such as `context.tex` containing AI question context are authoring aids,
not PDF inputs. Do not add them to the build graph.

## Metadata

`metadata.tex` remains readable LaTeX metadata. Release automation
requires exactly one `\newcommand{\version}{MAJOR.MINOR.PATCH}` declaration.
A supported SemVer-style prerelease suffix may follow the patch number. Keep
`\slug` equal to the registered `books.yml` slug. The manifest controls
automation participation; metadata controls LaTeX/PDF presentation and the
versioned filename. Similarly named title fields remain separately owned; manifest validation compares safely normalizable titles only as advisory warnings.

## Labels

New labels use `<course-prefix>:<type>:<descriptive-name>`. Existing prefixes are
`nt`, `la`, and `an`; common types include `ch`, `sec`, `ax`, `def`, `thm`, `lem`,
`prop`, `cor`, `ex`, `exc`, `prob`, `eq`, `fig`, and `tab`. Descriptive names
use ASCII letters or digits separated by single hyphens; uppercase letters are
allowed when they preserve meaningful notation, as in `an:thm:R-is-uncountable`.
Preserve legacy labels. Only replace a duplicate or broken label and update every
reference.

## Theorem environments

The public environments are `axiom`, `theorem`, `lemma`, `proposition`,
`corollary`, `definition`, `example`, `exercise`, `problem`, `solution`,
`remark`, and `proof`. Use `axiom` for assumptions that establish the formal
setting, and `definition` for new mathematical objects, properties, and
relations. Within each section, axiom through exercise share one numbered
sequence. Problem uses a separate section-scoped sequence. Solution and remark
are unnumbered; proof is the standard `amsthm` environment. Use `ax` as the
label type for numbered axioms.

### Mathematical prose conventions

Use introductory words according to their logical role:

- Use `Let` to define a new object or notation, or to choose a witness whose
  existence has already been established. Do not use it merely to introduce
  data or a structure whose existence is part of the current hypothesis.
- Use `Suppose` to introduce hypotheses and given data in definitions,
  statements, and proofs. This includes functions, relations, structured
  spaces, and membership conditions used to prove a universally quantified
  statement; the wording does not assert that such data exists for every
  possible choice of its parameters.
- Reserve `Assume` for a temporary assumption intended to lead to a
  contradiction, and make that purpose explicit when it is not already clear
  from the surrounding argument.
- Use `If` for conditional statements and case distinctions rather than as the
  routine opening of a proof step.

For example, write `Suppose $x \in S$.` when proving a property for every
element of a set that may be empty. After deriving `\exists x \in S, P(x)`,
write `Let $x \in S$ satisfy $P(x)$.` to select the established witness. Write
`Suppose $\sim$ is an equivalence relation on $S$.` or `Suppose $f:X\to Y$.`
when such a structure is given conditionally; write `Let $R \coloneqq
\cdots$.` when introducing a definition.

## Shared mathematics commands

Shared commands are defined in `common/styles/textbook-math.sty`; book-specific
additions belong in the owning book's `local-style.sty`. Check those files
before introducing or documenting a command.

The `\by{...}` command typesets a justification beside a displayed implication.
Its argument may contain prose, mathematics, or both. Wrap each mathematical
portion in `\ensuremath{...}`; do not use `$...$` or `$$...$$` inside `\by`.
For example:

```tex
\by{\Cref{an:ax:completeness}} \Downarrow
\by{\ensuremath{x \leq y}} \Downarrow
\by{\ensuremath{P(n)} is true} \Downarrow
```

This form works in the text-mode boxes created by `\by` without introducing
nested dollar-delimited math. It also prevents `latexindent` from mistaking the
inner dollars for a separate math block and consequently failing to recognize
the surrounding `array` environment.

## Draft annotations

Use `\todo{...}`, `\verify{...}`, and `\sourcecheck{...}` for unfinished prose,
mathematical checks, and provenance checks. They remain visible in PDFs.
Repository checks also report bare uppercase `TODO`, `VERIFY`, and `SOURCECHECK`
markers, including comments, as warnings rather than failures.

## Bibliographies and source notes

Each book uses BibLaTeX with the Biber backend. Its `references.bib` file is the
authoritative bibliography source; `sorting=none` preserves source order, and
`\nocite{*}` includes the complete source list even when the body has no citations.
Use prose or a footnote when no source-note environment is defined.
