# Mathematical Analysis I: formalization boundary

This document owns this book's mathematical prerequisites under the
[repository Lean policy](../../docs/formalization.md). Nothing here establishes
prerequisites for another book.

## Starting structures

Accept classical logic, ordinary sets and functions, equivalence relations and their correspondence with partitions,
finite sets, elementary finite sums and products, natural-number induction and
well-ordering, and basic integer and rational arithmetic and order. Accept the
real numbers as a complete ordered field, with the least-upper-bound property. Their construction from rationals is not
required. Accept the complex numbers with their basic field operations,
conjugation, and modulus.

## Accepted results

- Arithmetic and order identities in the number systems above, finite counting,
  and finite sum and product identities.
- Elementary finite-dimensional linear algebra: coordinate operations, bases,
  dimension, linear maps, Euclidean inner products, Cauchy-Schwarz, and the
  resulting norm and triangle inequalities.
- Basic set operations, images and inverse images, composition and restrictions,
  injections, surjections, bijections, and elementary finite/countable indexing.
  Subsets and images of finite sets, finite unions and products of finite sets,
  and extrema of nonempty finite totally ordered sets are accepted.
- Elementary countability in classical set theory with choice: subsets and images
  of at most countable sets, infinite subsets of countable sets, at most countable
  unions and finite products of at most countable sets; countability of the
  integers and rationals; uncountability of the reals and binary sequences;
  and Cantor's power-set theorem. These are prerequisites, not local core proofs.
  This does not authorize general cardinal arithmetic or other set-theoretic
  results beyond the stated boundary.

Accept the least-upper-bound and greatest-lower-bound properties of the reals,
the Archimedean property, density of the rationals, existence and uniqueness of
positive real nth roots, and geometric decay in the form: for every b > 1 and
epsilon > 0, some positive integer n satisfies b^(-n) < epsilon. Accept the
standard extended-real order, including suprema and infima of arbitrary subsets
and the empty-set conventions. These replace the removed number-systems chapter.
Do not infer acceptance of other equivalent completeness formulations or of
convergence and compactness theorems from this list.

## Results developed in this book

Develop basic metric topology and compactness, sequences and series, continuity, differentiation,
and Riemann-Stieltjes integration. In particular, prove monotone convergence,
Bolzano-Weierstrass, the Cauchy criterion, intermediate and extreme value
results, mean value results, and the fundamental theorem of calculus from the
accepted boundary and earlier local results. Do not cite their Mathlib
counterparts as shortcuts in the core proofs.

## Scoped external exceptions

No additional external theorem is initially approved. Real construction is
omitted by the starting boundary; Lebesgue integration and general functional
analysis are not alternative foundations for the integration chapter. Record
any future external exception with its location and reason before use.
