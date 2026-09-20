# Analytic Wronskian criterion: implementation status

The analytic criterion is still pending. The adapted basis and its
constant change-of-basis identity are now proved.

## Proved ingredients

- Nonrationality implies independence of the exact rational family on U
  and as analytic germs at each point of U.
- A scalar analytic function whose iterated derivatives all vanish has
  zero germ. Thus every nonzero coefficient combination has finite order.
- `exists_basis_distinct_orders` constructs a basis with distinct first
  nonzero indices for any separating sequence of linear forms on a
  finite-dimensional real vector space. Its proof uses induction on
  dimension, a minimal nonzero linear form, and its codimension-one kernel.
- `rationalFamily_exists_basis_distinct_orders` applies this construction
  to the derivative forms on coefficient space. It supplies an actual
  basis of the original coefficient space, so the change is constant and
  invertible, not a point-dependent change of functions.
- `wronskian_linearCombination_matrix` proves that a constant coefficient
  change C multiplies the Wronskian by det(C).
  `wronskian_basis_ne_zero_iff` transfers nonvanishing for a basis change.
- For distinct natural orders r_j, the matrix with entries
  (r_j).descFactorial(i) has nonzero determinant by the Vandermonde identity.

Files: AnalyticTaylorInjectivity.lean, WronskianLeadingMatrix.lean,
OrderedTaylorBasis.lean, RationalTaylorBasis.lean.

## Remaining proof

Prove the analytic leading-term formula for the Wronskian of a family
with distinct orders. For leading terms a_j t^(r_j), its proposed first
coefficient is the product of a_j times the descending-factorial determinant,
with exponent sum(r_j)-N(N-1)/2. In particular, the proof must handle
derivative orders larger than an individual r_j, not use truncated natural
subtraction as if negative powers were present.

After that, use the already proved basis change to obtain W_d not
identically zero and apply the existing escape theorem.
Theorem 1.2 is not yet claimed as fully formalized.

## Validation of the basis construction

Compiled OrderedTaylorBasis.lean and RationalTaylorBasis.lean in Lean
4.24.0 with warnings as errors. Audited the five new theorem declarations;
only propext, Classical.choice, Quot.sound occur transitively, without
sorryAx. This is targeted validation, not a new full CI success claim.
