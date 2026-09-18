# Elementary Number Theory: formalization boundary

This document owns this book's mathematical prerequisites under the
[repository Lean policy](../../docs/formalization.md), which governs standard
interfaces, independent proofs, and citations. These assumptions apply only to
this book.

## Starting structures

Accept classical logic, elementary sets and functions, and natural numbers and
integers with their arithmetic and order laws, induction, strong induction, and
well-ordering. Use the standard number types and explain any textbook convention
excluding zero.

## Accepted results

- Elementary arithmetic, order, finite sums and products, finite counting, and
  the finite pigeonhole principle.
- Rational arithmetic and elementary polynomial evaluation and identities when
  needed for formulas.

Well-ordering is assumed, but the quotient-remainder theorem and substantive
divisibility results are not part of the accepted arithmetic background.

## Results developed in this book

Develop the division algorithm, gcd and the Euclidean algorithm, Bezout's
identity, Euclid's lemma, prime factorization, congruences and the Chinese
remainder theorem, Fermat's and Euler's theorems, arithmetic functions, primitive
roots, and quadratic reciprocity. Develop selected later results on cryptography,
special number forms, Diophantine equations, sums of squares, Fibonacci numbers,
and continued fractions from this background and earlier local results.

Construct gcd and lcm locally and prove their characterizations before comparing
them with the standard definitions, including zero inputs. Use divisibility
through its elementary witness relation in these core proofs.

## Scoped external exceptions

Standard gcd/lcm specifications and elementary divisibility comparisons may be
used solely to identify the independently constructed values with the standard
ones after the local proofs. They do not supply the core arguments.

No other exceptions. Group orders and Lagrange's theorem are not prerequisites
for the core proofs of Fermat's or Euler's theorem; algebraic alternatives or
analytic applications require an explicit extension of this boundary.
