# Site metadata

## Registry fields

`books.yml` is the canonical source for repository title, short title, label
prefix, optional Lean module, status, ordering, and the `build`, `check`,
`release`, and `site` flags. The flags control participation in the all-books
build, repository-wide validation, official releases, and site publication
respectively.

An explicit `make books BOOK=<slug>` may build a registered book even when
`build` is false, while release preparation requires `build: true` and enables
`release: true`. A reviewed transition to `release: true` publishes the current
version; subsequent version increases publish new releases after main CI
succeeds. See [Releases](developer-workflow.md#releases).

Statuses describe publication state:

- `draft`: actively being written and not an official distribution
- `review`: planned material is largely present and under review
- `published`: an official versioned PDF is public
- `archived`: no longer actively maintained

A published book may continue to evolve. Status is descriptive; automation
participation is controlled separately by the boolean flags.

## Generated site pages

`make site` selects normalized `site: true` books and writes that metadata into
ignored `site/books/<slug>.md` page front matter for a local or CI build. Pass
`BOOK=<slug>` to limit generation to one site-enabled book.

`make site check` compares existing pages with the expected rendering without
writing files. It rejects stale, missing, and orphaned pages. Run `make site`
first in a clean checkout, where the ignored pages are absent. With
`BOOK=<slug>`, check mode validates only that book's page.

Publishing a book on the site requires `build: true` and `site: true` in
`books.yml`. Manifest validation rejects `site: true` with `build: false`.
After changing the manifest, follow [Refreshing local pages](#refreshing-local-pages)
and the applicable [validation requirements](CONTRIBUTING.md#validation-by-change-category).
Use `make check source` to validate fresh rendering in a temporary directory
when local site pages are not needed.

The build workflow downloads PDF artifacts to update the `generated-pdfs`
branch. Pages checks out that complete snapshot and stages only `site: true`
books as `pdf/<slug>.pdf`; PDFs for registered books with `site: false` are
ignored. The snapshot README comes from `.github/generated-pdfs-README.md`.

Book-page presentation rules live in `site/assets/book.css`; edit that
stylesheet when changing the shared book layout appearance or responsive
behavior.

The index discovers generated book pages through `site.pages`, sorts their front
matter by manifest order, and renders canonical titles and status labels. The
common book layout reads the same page front matter, including Lean coverage
generated from the proof index. No separate Jekyll data file is generated or
consumed, and generated pages are not tracked by Git. Separate book descriptions
are intentionally not supported.

Lean coverage is the number of LaTeX results linked to a Lean declaration through
the proof index divided by the book's LaTeX theorem, lemma, proposition, and
corollary count, expressed as a percentage rounded to one decimal place.
Each result counts once, even when it has multiple registered labels. Comments
and literal code samples are excluded; unlabeled results remain in the denominator.
Lean-only results do not belong in the proof index and do not contribute to coverage.
Coverage cannot exceed 100%. When the LaTeX count is zero, both the linked count
and the percentage are zero.

Status labels and the `short_title` fallback are defined once in the generator.
See [Repository architecture](ARCHITECTURE.md#metadata-and-automation) for
metadata ownership and automation policy.

## Refreshing local pages

After changing `books.yml`, theorem sources, or proof-index entries, run
`make site` and then `make site check` before a local Jekyll build. This refreshes
both publication status and Lean coverage; do not edit generated page front
matter or commit `site/books/`. A stale-page error reports local generated
state, not necessarily an invalid manifest. CI generates fresh pages for each
site build. `make check source` checks rendering in a temporary directory and
does not refresh or validate your existing local pages.
