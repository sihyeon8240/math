# Mathematical Analysis: formalization boundary

This document owns this book's mathematical prerequisites under the
[repository Lean policy](../../docs/formalization.md), which governs standard
interfaces, independent proofs, and citations. These assumptions apply only to
this book.

## Starting structures

Accept classical logic with choice, elementary sets and functions, finite sums
and products, induction and well-ordering, and basic arithmetic and order in the
usual number systems. Accept the real numbers as a complete ordered field via
the least-upper-bound property, without constructing them from rationals, and
the complex numbers with their field operations, conjugation, and modulus.

## Accepted results

- Elementary finite and countable set theory: finite counting, countable unions
  and finite products of at most countable sets, countability of the integers
  and rationals, uncountability of the reals and binary sequences, and Cantor's
  power-set theorem. General cardinal arithmetic is outside this boundary.
- Elementary finite-dimensional linear algebra through bases, dimension, linear
  maps, Euclidean inner products and norms, and Cauchy-Schwarz. Accept norm
  definitions, norm axioms, and elementary coordinate norm estimates. For
  multivariable analysis, also accept rank-nullity, determinants, and
  orthogonalization.
- Elementary real order theory: suprema and infima, the Archimedean property,
  density of the rationals, positive roots, and arbitrarily small reciprocal
  powers of a real number greater than one. Accept extended-real order and its
  empty-set conventions. This does not assume sequence convergence theorems or
  other characterizations of completeness.
- Elementary real and complex polynomial algebra through evaluation, degree
  rules, division, and the factor theorem.

## Results developed in this book

Develop metric topology, compactness and connectedness, sequences and series,
continuity, differentiation, and Riemann-Stieltjes integration. Core results
include monotone convergence, Bolzano-Weierstrass, the Cauchy criterion,
intermediate and extreme value theorems, mean value theorems, and the fundamental
theorem of calculus. Develop function sequences and series, uniform convergence
and interchange of limits, differentiation and integration, special functions,
multivariable differentiation and inverse/implicit function theorems,
integration of differential forms, and Lebesgue theory.

Topological properties, including closure and compactness properties and
continuity of coordinate maps, belong to this development. Finite-dimensional
norm equivalence is not a prerequisite for the initial metric topology. For
multivariable analysis, accept finite-dimensional norm equivalence and
continuity of linear maps. Use elementary ball, neighborhood,
open-complement, closed-cover, finite-subcover, epsilon, and open-preimage
characterizations as representation interfaces; they do not authorize importing
substantive topology.
Prove the limit-point characterizations of closedness and closure and the
separation characterization of connectedness locally. Connectedness includes
the empty set, and empty ambient spaces remain allowed.

Measure construction, measurable functions, Lebesgue integration, and its
convergence theorems are core developments. Standard measure and integral
representations do not authorize using their substantive properties as proof
shortcuts; different integral notions require a proved correspondence.

## Scoped external exceptions

None. Measure theory and functional analysis are not alternative prerequisites
for this book's integration theory. Manifold theory and general Stokes theorems
are not blanket prerequisites.
