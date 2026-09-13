# Mathematical Analysis II: formalization boundary

This document owns this book's mathematical prerequisites under the
[repository Lean policy](../../docs/formalization.md). Nothing here establishes
prerequisites for another book.

## Starting structures

Accept classical logic, ordinary sets and functions, equivalence relations,
natural-number induction and well-ordering, finite/countable indexing, and basic
arithmetic of the natural, integer, rational, real, and complex number systems.
Accept the real numbers as a complete ordered field and use the standard
finite-dimensional real and complex vector spaces.

## Accepted results

- Elementary metric topology, compactness and connectedness, numerical sequences
  and series, continuity, one-variable differentiation, and Riemann-Stieltjes
  integration as developed in Mathematical Analysis I. This includes monotone
  convergence for real sequences, Bolzano-Weierstrass, intermediate and extreme
  value theorems, mean value theorems, and the one-variable fundamental theorem
  of calculus. It does not include measure-theoretic convergence theorems.
- Finite-dimensional linear algebra: bases, dimension, linear maps and their
  matrix representations, rank-nullity, determinants, inner products,
  orthogonalization, and norms. Accept finite-dimensional norm equivalence and
  continuity of linear maps as external prerequisites for multivariable analysis.
- Elementary polynomial algebra over real and complex scalars: evaluation,
  degree rules, division, and the factor theorem.

These are accepted mathematical results even where the other textbook has not
yet formalized them. Use their Mathlib declarations rather than importing another
textbook. New subject matter added to Analysis I is not automatically added to
this boundary; amend this document if the accepted scope needs to grow.

## Results developed in this book

Prove the selected results about function sequences and series, uniform
convergence and interchange of limits, differentiation and integration,
special functions, multivariable differentiation and inverse/implicit function
theorems, integration of differential forms, and the Lebesgue theory.

In particular, measure construction, measurable functions, Lebesgue integration,
measure-theoretic convergence theorems, and the integration theorems taught here
are core developments, not prerequisites imported under the heading of analysis.
Mathlib's measure and integral definitions may be reused without accepting their
substantive properties as proof shortcuts. Check that the formal integral notion
and its hypotheses match the textbook; prove a bridge when changing integral
notions.

## Scoped external exceptions

No additional external theorem is initially approved. General measure theory,
functional analysis, manifold theory, and general Stokes theorems are not blanket
prerequisites. Any additional external theorem needs a recorded location and
reason before use, including in alternative proofs.
