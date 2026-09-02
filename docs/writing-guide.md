# Textbook writing guide

This guide describes the repository's supported authoring interface. Structural
instructions protect the build and generated sources and are requirements. Prose
and proof-layout conventions are recommendations: prefer them for consistency,
but depart from them when another form is clearer in context.

## Book structure and manifests

### Creating and registering a book

Create and register a book from the repository root with:

```sh
make new-book SLUG=<slug> TITLE="<title>"
```

The script copies `common/templates/`, creates the first chapter and section,
and registers the book in `books.yml`. The lower-level `books.py add` command
only registers an existing directory.

### Generated assembly and section files

Each generated `books/<slug>/book.tex` is the LaTeX entry point. Its
document-wide setup comes from the shared template, and its ordered `\include`
list comes from the contents manifest. Each chapter directory has an `index.tex`
that declares the chapter and inputs or includes its section files in reading
order.

Name a single-file logical section `NN-section-name.tex`. If it must be split,
keep the same logical number and slug in every source and add consecutive
suffixes beginning with `-a`, for example `02-main-result-a.tex` and
`02-main-result-b.tex`. Set `split` in `sections.yml` to the number of physical
files; the generator assigns consecutive suffixes from `a`. Do not use
context-dependent names such as `section-part-2`. See the canonical naming policy
in [the architecture guide](ARCHITECTURE.md#naming-conventions).

Generated `index.tex` declares each `\section` once. All single and split
section files contain only the section body; later parts continue that body
without repeating a heading. Split at a top-level boundary rather than inside
an environment. A theorem statement may end one
part and its separate `proof` environment may begin the next part.

### Contents manifests and metadata

Edit the `chapters` and optional `appendices` lists in `chapters.yml` and
their `sections.yml` files, then run `make contents all BOOK=<slug>`. Do not edit
the generated `book.tex` or any chapter `index.tex`. Chapter and section titles
may contain LaTeX, including `\texorpdfstring` where a PDF-safe form is required.
Slugs remain meaningful ASCII descriptions: preserve mathematical identifiers
and exponents (for example, `functions-of-class-l2` and `the-number-e`) instead
of deriving a lossy slug from rendered title text.

Edit manifest-owned metadata in `books.yml`, then run
`make contents chap BOOK=<slug>` to regenerate `book.tex`. Field ownership and
optional frontmatter overrides are defined in the
[architecture guide](ARCHITECTURE.md#metadata-and-automation).

### Authoring and style files

Section files do not load packages directly; `book.tex` loads the shared
`textbook` package and optional book-local `local-style` extensions.

Files such as `context.tex` containing AI question context are authoring aids,
not PDF inputs. Do not add them to the build graph.

## LaTeX document structure

### Theorem environments

The public environments are `axiom`, `theorem`, `lemma`, `proposition`,
`corollary`, `definition`, `example`, `exercise`, `problem`, `solution`,
`remark`, and `proof`. Use `axiom` for assumptions that establish the formal
setting, and `definition` for new mathematical objects, properties, and
relations. Within each section, axiom through exercise share one numbered
sequence. Problem uses a separate section-scoped sequence. Solution and remark
are unnumbered; proof is the standard `amsthm` environment. Use `ax` as the
label type for numbered axioms.

### Labels and references

New labels use `<course-prefix>:<type>:<descriptive-name>`. Use the owning
book's `label_prefix` from `books.yml`; do not copy a repository-wide prefix list
into documentation. The supported label syntax and structural policy are defined
in [the architecture guide](ARCHITECTURE.md#labels).
Preserve legacy labels. Only replace a duplicate or broken label and update every
reference. Put a numbered environment's `\label` on the same source line as its
`\begin{...}` declaration so that the environment and its repository-global
identifier remain visibly paired.

### Bibliographies and source notes

Each book uses BibLaTeX with the Biber backend. Its `references.bib` file is the
authoritative bibliography source; `sorting=none` preserves source order, and
`\nocite{*}` includes the complete source list even when the body has no citations.
Use prose or a footnote when no source-note environment is defined.

## Mathematical writing

### Logical introductions

Prefer introductory words that reflect their logical role:

- Prefer `Let` to define a new object or notation, or to choose a witness whose
  existence has already been established. The imperative `Define ...` is also
  natural when explicitly introducing an object, function, or notation. For
  data or a structure supplied by the current hypothesis, `Suppose` is usually
  clearer.
- Prefer `Suppose` to introduce hypotheses and given data in definitions,
  statements, and proofs. It may also restrict attention to a case
  whose complement makes the desired conclusion immediate.
- `Assume` is particularly useful for a temporary assumption, especially in a
  proof by contradiction. Make its temporary role clear when the surrounding
  argument does not already do so.
- Prefer `If` for conditional statements and case distinctions. A direct
  `Suppose` or `Assume` often reads more naturally when opening a proof step.

Keep the distinction when deriving a contradiction. A contradiction obtained
after `Suppose $x \in S$` establishes the conditional conclusion $x \notin S$;
If nonemptiness of $S$ has already been established and the argument
needs an actual element to reach a contradiction, write `Let $x \in S$`.
Likewise, when proving uniqueness, choose one established witness with `Let`,
but introduce an arbitrary competing candidate conditionally with `Suppose`.

### Arbitrary variables

When a proof fixes an element, proves a pointwise claim, and then changes to a
set-level or universally quantified conclusion, an explicit discharge can make
the scope clear:

```tex
Suppose $x \in A$.
% Derive P(x).
Since $x \in A$ was arbitrary,
\[
  \forall x \in A, P(x).
\]
```

Avoid `is arbitrary` at introduction. When using `was arbitrary` at discharge,
include the domain rather than writing only `Since $x$ was arbitrary`. The
discharge may be omitted when the scope and conclusion are already clear. In
particular, it is usually unnecessary when the proof obligation or preceding
statement binds the variable with `\forall`, when a structural label such as
`Surjectivity`, `Reflexivity`, `($\subseteq$)`, or `($\supseteq$)` makes
the pointwise obligation explicit, or when the variable is an existential
witness or remains local.

An arbitrary-element argument is valid even when its domain is empty, but it
does not prove that the domain is nonempty. Establish nonemptiness separately
before choosing an element or taking a minimum or maximum.

### Definitions and equalities

Prefer `\coloneqq` when an explicit formula introduces new notation or a new
object, including pointwise definitions of functions and sequences and notation
introduced with `where` or `say`. The ordinary equals sign remains appropriate
for asserted equalities, calculations, equations, and the selection of a
particular value. Thus write `Define $f$ by
$f(x) \coloneqq x^{2}$.` and `where $e_{1} \coloneqq (1,0,\dots,0)$`, but
write `Let $\varepsilon = 1$.` when choosing a value and retain `=` in a
condition such as `x=y`.

### Terminology and emphasis

Prefer `\textbf{...}` for a term at the point where it is defined and
`\emph{...}` for ordinary rhetorical emphasis and conventional proof
qualifiers. If without loss of generality is abbreviated, prefer `\emph{WLOG}`;
spelling out the phrase is equally acceptable.

### Proof organization

For proofs with repeated structural obligations, consider bold item labels such
as `Injectivity` and `Surjectivity`, or `Base case` and `Inductive step`. Long
chains of short implications may be displayed in an `array` with `\Downarrow`;
when a step needs an explicit justification, use `\by{...}` as described below.
These layouts are conventions for recurring proof shapes, not requirements for
proofs that read more clearly as prose.

## LaTeX source conventions

### Command ownership

Shared commands are defined in `common/styles/textbook-math.sty`; book-specific
additions belong in the owning book's `local-style.sty`. Check those files
before introducing or documenting a command.

### Braces in command arguments and scripts

For consistent LaTeX source, prefer braces around every mandatory command
argument and every subscript or superscript argument, even when the argument is
a single character. This preference applies to both single- and multi-character
arguments. For example, write `\frac{1}{n}`, `N_{r}(p)`, `\mathcal{G}_{2}(b)`, and
`x^{2}` rather than `\frac 1n`, `N_r(p)`, `\mathcal G_2(b)`, and `x^2`.

### Displayed justifications with `\by`

The `\by{...}` command typesets a justification beside a displayed implication.
Its argument may contain prose, mathematics, or both. Wrap each mathematical
portion in `\ensuremath{...}`; do not use `$...$` or `$$...$$` inside `\by`.
For example:

```tex
\by{\Cref{an:ax:completeness}} \Downarrow
\by{\ensuremath{x \leq y}} \Downarrow
\by{\ensuremath{I} is a \ensuremath{k}-cell in \ensuremath{\R^{k}}} \Downarrow
```

This form works in the text-mode boxes created by `\by` without introducing
nested dollar-delimited math. It also prevents `latexindent` from mistaking the
inner dollars for a separate math block and consequently failing to recognize
the surrounding `array` environment.
