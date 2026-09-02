# Documentation map

The root [README](../README.md) is the repository overview and quick start. This
directory separates stable policy, task-oriented instructions, and explanatory
context so that a rule has one authoritative home.

## Choose a guide

| Document | Primary audience | Role |
|---|---|---|
| [Repository architecture](ARCHITECTURE.md) | All contributors | Authoritative structure, ownership, naming, metadata, and stability contract. |
| [Contributing](CONTRIBUTING.md) | Contributors | Submission requirements, checks, rights, new-book workflow, and releases. |
| [Textbook writing guide](writing-guide.md) | Authors and editors | Supported LaTeX authoring interface and content conventions. |
| [Lean formalization](formalization.md) | Formalization contributors | Trust boundary, namespace policy, proof links, and Mathlib dependencies. |
| [Developer workflow](developer-workflow.md) | Repository developers | Day-to-day commands, CI behavior, development PDF publication, and release operations. |
| [Maintainer guide](maintainer-guide.md) | Maintainers and reviewers | Risk-based review and publication checklists. |
| [Site metadata](site-metadata.md) | Site maintainers | Manifest statuses, automation flags, and generated site pages. |
| [Design decisions](design-decisions.md) | Future maintainers | Rationale and tradeoffs behind the architecture; not a second policy source. |

Book structure and references live in each `books/<slug>/` source tree. Generated
files and their ownership are documented in the architecture guide. `AGENTS.md`
contains instructions for automated coding agents rather than contributor
documentation.
When documents appear to disagree, follow [Repository architecture](ARCHITECTURE.md)
for structural policy and `books.yml` for current book metadata and automation
flags. Treat the Makefile and `make help` as the current public command interface,
then update stale prose rather than preserving a contradiction.
