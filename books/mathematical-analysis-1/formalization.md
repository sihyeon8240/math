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
positive real nth roots, and geometric decay in the form: for every $b > 1$ and
$\varepsilon > 0$, some positive integer $n$ satisfies $b^{-n} < \varepsilon$. Accept the
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

## Definitions and proof dependencies

Use Mathlib's standard predicates and operations as the public mathematical
interface: `IsOpen`, `IsClosed`, `interior`, `closure`, `frontier`, `derivedSet`,
`Bornology.IsBounded`, `Perfect`, `Dense`, `IsCompact`, and `Filter.Tendsto`.
Explain them using balls, limit points, finite open subcovers, and epsilon
conditions. State and prove the needed characterizations rather than defining
parallel collections of open, closed, or compact sets. Use `Metric.ball` for
open balls and `nhds` for general neighborhoods; a neighborhood need not be open.
Use `IsPreconnected` for the book's connectedness convention, which includes
the empty set, and prove its separation characterization before the interval
result. `IsConnected` additionally requires nonemptiness.
Retain the book's empty-space, empty-set, zero-dimensional, and zero-based
sequence conventions. In particular, boundedness must not require the ambient
space to be nonempty.

Reuse standard real and Euclidean types, metric structures and their distance
axioms, balls, subtypes with the inherited distance, and finite products with the
maximum distance. Their distance formulas and elementary coordinate norm
inequalities fall within the accepted arithmetic and finite-dimensional linear
algebra boundary. This does not accept topological properties of those spaces.

The standard topology and filter interfaces may encode these definitions.
Use their ball, neighborhood, open-complement, finite-open-subcover, and epsilon
characterizations only as representation bridges. Prove the ball and separation
characterizations needed by subsequent arguments explicitly. Standard notation
may be used from the outset; it does not authorize invoking the corresponding
substantive Mathlib theorems. In particular, the closed-set and closure bridges
require the local limit-point arguments; they are not extra assumed topological
theorems. The closed-cover characterization of preconnectedness is a
representation interface; the separation bridge uses the locally proved closure
properties. The open-preimage characterization of continuity is likewise a
definition interface, not permission to import continuity results.

No substantive topological or analytic result is accepted merely because it is a
short Mathlib helper. Prove closure properties, compactness properties, and the
continuity of the coordinate maps needed for finite boxes locally. For the latter,
use the maximum product distance and the Euclidean sum-of-squares formula,
including dimension zero; do not assume equivalence of finite-dimensional norms
or invoke an external coordinate-continuity theorem. Subsequent proofs reuse
these local results. Arithmetic, finite sums, and logical automation must stay
within the accepted boundary; simplification must not supply missing topology.

The current checked development covers metric topology, compactness and real
connectedness in Chapter 1 and the introductory sequence results in Chapter 2.
The same rules apply as later sections are formalized; this policy does not claim
that the remaining chapters have already been checked.

## Scoped external exceptions

No additional external theorem is initially approved. Real construction is
omitted by the starting boundary; Lebesgue integration and general functional
analysis are not alternative foundations for the integration chapter. Record
any future external exception with its location and reason before use.
