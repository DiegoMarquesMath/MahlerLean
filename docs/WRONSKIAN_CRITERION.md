# Analytic Wronskian criterion: implementation status

The criterion is still pending. This document distinguishes the proved
ingredients from the remaining argument.

## Proved

- Nonrationality implies independence of the exact rational family,
  globally on U and as analytic germs at every point of U.
- An analytic scalar function with every iterated derivative zero has
  zero germ, via its Taylor series.
- Every nonzero coefficient combination of the rational family therefore
  has a finite first nonzero derivative at each point of U.
- For distinct natural orders r_j, the matrix with entries
  (r_j).descFactorial(i) has nonzero determinant. Its determinant equals
  that of the Vandermonde matrix on the r_j.

The last identity handles the algebraic matrix expected in the leading
term of a Wronskian. It does not yet assert that this matrix is the leading
coefficient of the actual analytic Wronskian.

Files: AnalyticTaylorInjectivity.lean and WronskianLeadingMatrix.lean.
All five declarations compile with warnings as errors, and their transitive
axioms are only propext, Classical.choice, Quot.sound.

## Remaining

1. Construct a constant invertible change of basis of the finite-dimensional
   space of analytic germs so that the basis has distinct orders of vanishing.
2. Prove the leading-term formula for the Wronskian of that basis. If its
   leading terms are a_j t^(r_j), the proposed leading coefficient is
   the product of a_j times the descending-factorial determinant, with
   exponent sum(r_j)-N(N-1)/2.
3. Transfer nontriviality through the constant change of basis, then apply
   the result to rationalFamily and the existing escape theorem.

These are mathematical proof obligations in Lean. No theorem with them
hidden as axioms, sorry, or an assumed counting estimate has been introduced.
Theorem 1.2 is not yet claimed as fully formalized.
