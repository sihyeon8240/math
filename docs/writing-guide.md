# Textbook writing guide

This guide describes the repository's supported authoring interface. Structural
instructions protect the build and generated sources and are requirements. The
paired exposition format below is required for new or mathematically revised
theorems selected for formalization. Other prose and proof-layout conventions
are recommendations: prefer them for consistency, but depart from them when
another form is clearer in context.

Follow the [Lean-first authoring policy](formalization.md#authoring-policy)
before applying the paired exposition format in this guide.

## Book structure and manifests

### Creating and registering a book

Create and register a book from the repository root with:

```sh
make new-book SLUG=<slug> TITLE="<title>"
```

The script copies `common/templates/`, creates the first chapter and section,
and registers the book in `books.yml`. The lower-level `books.py add` command
only registers an existing directory.

The scaffold includes `formalization.md` from the
[formalization boundary template](../common/templates/formalization.md). Complete
its book-specific starting assumptions, accepted results, core developments,
and external exceptions before adding formalized results. Record Mathlib
correspondences in Lean comments under the [citation policy](formalization.md#statements-and-citation-policy).
The template supplies no common mathematical prerequisites.

### Generated assembly and section files

Each generated `books/<slug>/book.tex` is the LaTeX entry point. Its
document-wide setup comes from the shared template, and its ordered `\include`
list comes from the contents manifest. Each chapter or appendix directory has
a generated `index.tex`
that declares the chapter and inputs its section files in reading order.
Appendices use A, B, ... numbering and precede the bibliography backmatter.

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

### Paired mathematical exposition and Lean code

For new or mathematically revised theorems selected for formalization, present
mathematical explanation together with the corresponding Lean code:

- Keep the statement in its numbered mathematical environment with its label.
  Pair the natural-language statement with the corresponding Lean declaration
  signature, preserving domains, hypotheses, quantifiers, and conclusion.
- Keep the proof in a separate `proof` environment. Organize it into successive
  mathematical reasoning units, each with an explanation followed by the
  corresponding Lean proof fragment. A unit may contain several tactics; do not
  divide the exposition mechanically at every code line.
- Write the explanations so that they form a readable mathematical proof even
  when the code is skipped. Explain constructions, deductions, and necessary
  calculations rather than tactic syntax or implementation details. Expand
  automated reasoning when its mathematical justification matters to the reader.
- Keep fragments in proof order and make their dependence on preceding steps
  clear. A displayed fragment may rely on the declaration context and earlier
  fragments; it need not be a standalone Lean program.

Apply this format gradually when relevant mathematics is revised. Unrelated
edits do not require converting existing exposition, and motivation, historical
notes, and unformalized examples may remain ordinary prose. The format does not
establish common mathematical prerequisites across books.

The checked Lean source remains authoritative for the formal statement and
proof. Follow the [displayed-code policy](formalization.md#displayed-code-correspondence)
when copying or updating code in the exposition. This format specifies content
and reading order; it does not prescribe a particular LaTeX macro, frame, or
page layout.

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
if nonemptiness of $S$ has already been established and the argument
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

These are editorial preferences, not mechanically checked correctness rules.
Prefer an introduction that states the variable's domain explicitly rather than
merely saying it `is arbitrary`. When using `was arbitrary` at discharge,
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

Organize proofs around mathematical deductions, with enough prose to connect
each step to its purpose. For formalized results, use the paired format above.
Bold labels such as `Injectivity`, `Surjectivity`, `Base case`, and `Inductive
step` are optional aids for repeated obligations. Displayed implication chains
in an `array` with `\Downarrow` are also optional within an explanation; use
`\by{...}` when a displayed step needs a justification. These devices supplement
the explanation and do not replace the required explanation/code pairing.

## LaTeX source conventions

### Command ownership

Shared commands are defined in `common/styles/textbook-math.sty`; book-specific
additions belong in the owning book's `local-style.sty`. Check those files
before introducing or documenting a command.

### Paired mathematical prose and Lean code

The shared `lean` environment takes mathematical prose as its argument and
literal Lean code as its body. It prints the code in a monospaced, bordered box;
do not nest a `verbatim` environment inside it.

```tex
\begin{lean}{The two remainders are equal: $r'=r$.}
  have hrr : r' = r := by rw [hqq] at ha'; linarith
\end{lean}
```

Keep the closing `\end{lean}` on its own line. The formatter preserves
relative Lean indentation, but aligns the block to the surrounding environment
and condenses consecutive blank lines. Format the prose argument manually.
Put only mathematical statements in the prose, without step titles or
explanations of Lean commands.

Each explanation/code pair is a `minipage` and cannot split across pages.
Keep a pair shorter than one text page. Split long arguments into consecutive
mathematical reasoning units with their corresponding code; do not reduce font
size or omit reasoning merely to fit a box. Review the rendered pages for large
blank areas, overflow, and awkward transitions.

### Fonts and Unicode

Store text sources as UTF-8 with LF line endings. Choose characters for their
mathematical or linguistic meaning; font coverage must not determine the
statement or the checked Lean source. Do not introduce invisible format
characters, nonbreaking spaces, or look-alike characters merely to adjust
layout. Use LaTeX spacing commands in prose. When a language or a checked
identifier needs combining characters, preserve them deliberately rather than
applying a blanket Unicode normalization or ASCII conversion.

| Context | Source convention |
|---|---|
| LaTeX mathematical prose | Use math mode and the existing macros, such as `$\N$`, `$\N^{+}$`, and `$\bigcup_i E_i$`; do not paste a bare mathematical Unicode glyph into ordinary text as a font workaround. |
| Ordinary prose and PDF bookmark strings | Unicode appropriate to the language and supported by the selected text font is allowed; preserve existing `\texorpdfstring` alternatives. |
| Checked Lean and displayed Lean | Keep the actual identifiers and notation, including `ℕ`, `ℕ+`, `⋃`, and `⋂`. Displayed fragments must follow the [checked-source correspondence policy](formalization.md#displayed-code-correspondence). |
| Typesetting fixtures | Literal glyph inventories are allowed and must be identified as rendering specimens, not checked mathematical proofs. |

`common/styles/textbook-code.sty` owns the Lean code font configuration for all
books. The primary faces are the TeX Live files `DejaVuSansMono.ttf`,
`DejaVuSansMono-Oblique.ttf`, `DejaVuSansMono-Bold.ttf`, and
`DejaVuSansMono-BoldOblique.ttf`. LuaLaTeX fills missing glyphs from the explicit
fallback `texgyretermes-math.otf`. This includes the indexed union and intersection
characters U+22C3 (`⋃`) and U+22C2 (`⋂`), which the primary font lacks. There is no
claim that this font combination covers every Unicode character.

Add or change code fonts in the common style, using files supplied by the
supported TeX Live environment. Do not copy the fallback configuration into
individual books, depend on an undeclared workstation font, replace a symbol
with a visually similar character, or hide a missing-character diagnostic.
Fallback glyphs can differ in width, weight, or baseline from the monospaced
face; visual inspection remains necessary.

For new notation, extend the inventory in
[`tests/fixtures/lean-glyphs.tex`](../tests/fixtures/lean-glyphs.tex).
[`tests/fixtures/lean-fonts.tex`](../tests/fixtures/lean-fonts.tex) renders it
through the real `lean` environment in regular, italic, bold, and bold italic,
including syntax-highlighter styling. Run the focused check with:

```bash
python3 -m unittest discover -s tests -p 'test_code_fonts.py' -v
```

The test checks compilation, font-shape warnings, and the strict log checker;
it retains the review PDF at `build/font-check/lean-fonts.pdf`. It runs under
`make test` when `latexmk`, `lualatex`, and `latexminted` are available. A skip
in an environment without those tools does not validate glyph coverage: run
it in the supported textbook build environment before accepting a font change.
Review the specimen for recognizable symbols, baseline alignment, line wraps,
and clipping. Also inspect affected textbook pages.

A missing-character diagnostic is already a build error in
`scripts/check-log.py`, even without `--strict`; strict mode additionally rejects
overfull boxes. Shared font changes require `make test` and `make check all
strict` under the [validation policy](CONTRIBUTING.md#validation-by-change-category).
Text mathematical fonts remain separate from code fonts; see the
[`unicode-math` decision](design-decisions.md#unicode-math-and-code-fonts).

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
\by{the preceding lemma} \Downarrow
\by{\ensuremath{x \leq y}} \Downarrow
\by{\ensuremath{n} is positive} \Downarrow
```

This form works in the text-mode boxes created by `\by` without introducing
nested dollar-delimited math. It also prevents `latexindent` from mistaking the
inner dollars for a separate math block and consequently failing to recognize
the surrounding `array` environment.
