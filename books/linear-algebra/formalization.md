# Linear Algebra: formalization boundary

This document owns this book's mathematical prerequisites under the
[repository Lean policy](../../docs/formalization.md). Nothing here establishes
prerequisites for another book.

## Starting structures

Accept classical logic, ordinary sets and functions, equivalence relations,
natural-number induction, finite sets, and elementary finite sums and products.
Accept fields and their algebraic laws, and the basic arithmetic of the real and
complex numbers, including real order, nonnegative square roots, complex
conjugation, and modulus. Use Mathlib's standard vector-space and linear-map
structures as representations; their presence does not make linear-algebra
results prerequisites.

## Accepted results

- Field arithmetic, finite counting, finite sum and product identities, and
  elementary real inequalities.
- Elementary number theory of the integers: divisibility, the division
  algorithm, gcd and the Euclidean algorithm, Bezout's identity, Euclid's lemma,
  prime factorization, and basic congruence arithmetic. These are accepted
  prerequisites, including when reviewed in this book; cite their Mathlib
  declarations rather than importing the number-theory textbook. This does not
  authorize advanced number theory or transfer integer results to polynomials
  or matrices without the corresponding mathematical justification.
- Polynomial evaluation, degree and coefficient rules, polynomial division over
  a field, the factor theorem, root bounds, and polynomial gcd/Bezout identities.

Do not use polynomial facts about matrices, minimal polynomials, or characteristic
polynomials as prerequisites merely because scalar polynomial algebra is allowed.

## Results developed in this book

Prove finite-dimensional basis existence and extension, dimension and exchange
results, linear-map and matrix correspondence, rank-nullity, orthogonality and
Gram-Schmidt, determinant properties, eigenvalue and eigenspace results, spectral
results, triangulation, Cayley-Hamilton and primary decomposition, and the
selected convex-set results. Establish the needed properties of vector spaces,
linear maps, and matrices rather than taking those core properties from Mathlib.

## Scoped external exceptions

- Accept the fundamental theorem of algebra where complex eigenvalue existence
  and triangularization require polynomial splitting. Cite it at first use;
  prove the linear-algebra consequences locally.

Other external results require an amendment identifying their scope and reason.
This includes arbitrary-dimensional basis existence and analytic compactness or
separation theorems used in the convex-sets chapter; they are not implicitly
approved by the finite-dimensional or real-arithmetic prerequisites.
