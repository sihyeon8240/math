# Elementary Number Theory: formalization boundary

This document owns this book's mathematical prerequisites under the
[repository Lean policy](../../docs/formalization.md). Nothing here establishes
prerequisites for another book.

## Starting structures

Accept classical logic, ordinary sets and functions, equality and equivalence
relations, finite sets, and elementary finite sums and products. Accept natural
numbers and integers with their basic arithmetic and order laws, induction,
strong induction, and well-ordering of the natural numbers. Use Mathlib's
standard number types; explain any textbook convention excluding zero.

## Accepted results

- Arithmetic identities, order compatibility, cancellation, and elementary
  inequalities in natural numbers and integers.
- Basic finite counting, reindexing of finite sums and products, and the
  pigeonhole principle for finite sets.
- Rational arithmetic and elementary polynomial operations, including evaluation
  and algebraic identities, when needed for formulas.

Well-ordering is an accepted prerequisite, even if its formulation is restated
in the preliminaries. Acceptance of basic integer arithmetic does not include
the quotient-remainder theorem or substantive divisibility results.

## Results developed in this book

Prove the division algorithm, gcd properties and Bezout's identity, Euclid's
lemma and unique prime factorization, prime-number results, congruence results
and the Chinese remainder theorem, Fermat's and Euler's theorems, arithmetic
function identities, primitive-root results, and quadratic reciprocity. Develop
the results selected from the later chapters on cryptography, special number
forms, Diophantine equations, sums of squares, Fibonacci numbers, and continued
fractions in the same order from the accepted boundary.

Introduce the number-theoretic definitions needed by each development explicitly.
In the current gcd development, define the nonnegative gcd locally from a least
positive integer linear combination, with value zero for the zero pair. Prove
its common-divisor, greatestness, and uniqueness properties before using them;
do not obtain them from a Mathlib gcd characterization. Integer divisibility
uses the defining relation `a ∣ b ↔ ∃ k : ℤ, b = a * k`, with its witnesses
expanded directly in proofs.

No substantive number-theoretic property, even a short supporting lemma, is an
accepted prerequisite merely because Mathlib supplies it. Prove needed properties
from the accepted arithmetic and logical boundary and earlier local results.
Elementary type conversions and the standard number types remain permitted.

## Scoped external exceptions

No additional external theorem is initially approved. In particular, group
orders and Lagrange's theorem are not prerequisites for the core proofs of
Fermat's or Euler's theorem. An algebraic alternative proof or an application of
analysis in prime distribution requires a documented exception specifying the
result, its location, and its purpose before use.
