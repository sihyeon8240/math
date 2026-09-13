# Formalization boundary

This document owns this book's mathematical prerequisites under the
[repository Lean policy](../../docs/formalization.md). Nothing here establishes
prerequisites for another book.

> Authoring template: replace the prompts below with this book's decisions
> before adding formalized results. No mathematical prerequisites are supplied
> by this template. This file is maintained by the book's authors, not regenerated.

## Starting structures

Specify the logic, foundational principles, number systems, and other structures
accepted at the start. Distinguish the logic being studied from Lean's metatheory.
State which constructions or characterizing properties are assumed and which
will be developed. Do not inherit another book's assumptions implicitly.

## Accepted results

List the mathematical results that may be cited without local proof, with enough
detail to delimit their scope. Identify any accepted results from other subjects;
use Mathlib rather than importing another textbook. Routine supporting lemmas
must remain within this book's stated boundary.

## Results developed in this book

Identify the core results and their intended dependency order. State significant
exclusions from the prerequisite list, especially when Mathlib's standard
structures already provide properties that this book intends to prove.

## Scoped external exceptions

List each additional external theorem, where it may be used, and why it is needed,
including exceptions for separately labeled alternative proofs. Write "None" if
there are no exceptions. Amend this policy together with the first use of any
substantive external result outside the existing boundary.
