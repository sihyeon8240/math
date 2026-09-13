# Site metadata

## Registry fields

`books.yml` is the canonical source for repository title, short title, label prefix, optional Lean module, status, ordering, and the `build`, `check`, `release`, and `site` flags. The flags control participation in the all-books build, repository-wide validation, official releases, and site publication respectively. An explicit `make books BOOK=<slug>` may build a registered book even when `build` is false, while `make publish` requires `release: true`.

Statuses describe publication state:

- `draft`: actively being written and not an official distribution
- `review`: planned material is largely present and under review
- `published`: an official versioned PDF is public
- `archived`: no longer actively maintained

A published book may continue to evolve. Status is descriptive; automation participation is controlled separately by the boolean flags.

## Generated site pages

`make site` selects normalized `site: true` books and writes that metadata into ignored `site/books/<slug>.md` page front matter for a local or CI build; pass `BOOK=<slug>` to limit generation to one site-enabled book. `make site check` validates the same rendering without writing files and accepts the same optional scope. Because `site/books/` is ignored and may not exist in a clean checkout, check mode validates rendering in memory when it is absent; when local generated pages exist, it also rejects stale, missing, and orphaned pages.

Publishing a book on the site requires `build: true` and `site: true` in `books.yml`. After changing the manifest, run `make site check` and the repository checks; run `make site` only when local Jekyll input is needed. Manifest validation rejects `site: true` with `build: false`.

The build workflow downloads PDF artifacts to update the `generated-pdfs`
branch. Pages checks out that complete snapshot and stages only `site: true`
books as `pdf/<slug>.pdf`; PDFs for registered books with `site: false` are
ignored. The snapshot README comes from `.github/generated-pdfs-README.md`. Book-page presentation rules live in `site/assets/book.css`; edit that stylesheet when changing the shared book layout appearance or responsive behavior.

The index discovers generated book pages through `site.pages`, sorts their front matter by manifest order, and renders canonical titles and status labels. The common book layout reads the same page front matter, including Lean coverage generated from the proof index. No separate Jekyll data file is generated or consumed, and generated pages are not tracked by Git. Separate book descriptions are intentionally not supported.

Status labels and the `short_title` fallback are defined once in the generator. See [Repository architecture](ARCHITECTURE.md#metadata-and-automation) for metadata ownership and automation policy.

## Refreshing local pages

After changing `books.yml`, theorem sources, or proof-index entries, run
`make site` and then `make site check` before a local Jekyll build. This refreshes
both publication status and Lean coverage; do not edit generated page front
matter or commit `site/books/`. A stale-page error reports local generated
state, not necessarily an invalid manifest. CI generates fresh pages for each
site build. `make check source` checks rendering in a temporary directory and
does not refresh or validate your existing local pages.
