# Linear Algebra: formalization boundary

This document owns this book's mathematical prerequisites under the
[repository Lean policy](../../docs/formalization.md), which governs standard
interfaces, independent proofs, and citations. These assumptions apply only to
this book.

## Starting structures

Accept classical logic, elementary sets and functions, induction, finite counting,
and finite sums and products. Accept fields and the basic arithmetic of the real
and complex numbers, including real order, nonnegative square roots, complex
conjugation, and modulus.

## Accepted results

- Elementary integer number theory through divisibility, the division and
  Euclidean algorithms, gcd and Bezout's identity, prime factorization, and
  basic congruences.
- Elementary polynomial algebra over a field through evaluation, degree rules,
  division, the factor theorem, root bounds, and gcd/Bezout identities.

Scalar polynomial facts do not automatically supply corresponding results about
matrices, minimal polynomials, or characteristic polynomials.

## Results developed in this book

Develop finite-dimensional vector spaces, bases and exchange, dimension, linear
maps and matrices, rank-nullity, orthogonality and Gram-Schmidt, determinants,
eigenvalues, spectral results, triangulation, Cayley-Hamilton, primary
decomposition, and the selected convex-set results.

Standard vector-space and linear-map structures represent the objects; their
availability does not make these results prerequisites. Arbitrary-dimensional
basis existence and analytic compactness or separation theorems are outside the
accepted background.

## Scoped external exceptions

Accept the fundamental theorem of algebra for complex eigenvalue existence and
triangularization, where polynomial splitting is needed. Prove its
linear-algebra consequences locally.
