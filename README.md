# Undergraduate Mathematics Textbooks

This book-oriented monorepo manages undergraduate mathematics textbooks written in LaTeX as versioned works in progress. Textbook content and repository code use different licenses; see [Licensing](#licensing).

Every book can continue to change and expand. A successful build confirms that the current source compiles, not that its mathematics is complete or free of errors.

## Books

[`books.yml`](books.yml) is the canonical textbook registry. Book-local `chapters.yml` and `sections.yml` files are the canonical contents hierarchy and generate LaTeX assembly.

## Quick start

The easiest supported setup is the development container. Local setup requirements are documented in the [developer workflow](docs/developer-workflow.md); `make doctor env` verifies them. Then run:

```sh
make doctor env
make books BOOK=linear-algebra
```

Use `make help` for the complete command interface. Common tasks are:

| Task | Command |
|---|---|
| Build one or all enabled books | `make books [BOOK=<slug>]` |
| Build and check selected books' LaTeX logs | `make books [BOOK=<slug>] check [strict]` |
| Run both independent validation suites | `make test`, then `make check all strict` |
| Inspect repository or book health | `make report`, `make doctor books [BOOK=<slug>]` |
| Create a textbook | `make new-book SLUG=<slug> TITLE="<title>"` |

See the [developer workflow](docs/developer-workflow.md) for formatting, generated content, focused checks, CI, and release commands.

## Repository layout

- `books/<slug>/`: independently assembled textbooks, each entered through `book.tex`
- `common/`: shared LaTeX styles, assets, and book templates
- `config/`: canonical container image and development toolchain versions
- `lean/` and `proof-index/`: formalizations and links to textbook statements
- `scripts/` and `tests/`: repository automation and its tests
- `site/`: website source; generated book pages are ignored
- `docs/`: architecture, contribution, authoring, and maintenance guides

Build output belongs only under the ignored `build/` directory. See the [repository architecture](docs/ARCHITECTURE.md) for file ownership, assembly rules, metadata, and generated files.

## Formal verification

Lean kernel-checks selected statements; it does not certify an entire textbook. Verified LaTeX statements are linked to checked declarations through chapter-owned proof-index entries. See the [Lean formalization guide](docs/formalization.md) for the trust boundary and workflow.

## Contributing

Report errors with the book and source location. Before submitting changes, read the [contributing guide](docs/CONTRIBUTING.md); authors should also follow the [textbook writing guide](docs/writing-guide.md).

## Licensing

Textbook content remains under the terms recorded in [LICENSE-CONTENT](LICENSE-CONTENT), currently CC BY 4.0. Repository code and automation are under the [MIT License](LICENSE-CODE), including `scripts/`, the `Makefile`, repository-authored build, validation, distribution and release automation, repository-authored workflow and development-environment configuration, and `common/styles/`. This does not apply MIT to textbook content, trademarks, or third-party material. External dependencies remain under their own licenses.

## Documentation

The [documentation map](docs/README.md) directs contributors, authors, and maintainers to the authoritative guide for each task. Structural policy lives in the [repository architecture](docs/ARCHITECTURE.md), while current book metadata and automation flags live in `books.yml` and are explained in [site metadata](docs/site-metadata.md).
