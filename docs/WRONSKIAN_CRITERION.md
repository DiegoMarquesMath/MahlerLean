# Analytic Wronskian criterion

The leading-term formula and its application to the manuscript's rational
family are proved. Wronskian nontriviality is no longer an extra assumption
in the analytic nonrational escape theorem.

## Leading term

For analytic functions φ_j at z with distinct finite vanishing orders r_j,
put a_j = φ_j^(r_j)(z)/r_j! and S = sum_j r_j - N(N-1)/2.
The theorem `tendsto_wronskian_div_pow` proves

    W(φ)(x) / (x-z)^S → (product_j a_j) det(Vandermonde(r))

on the punctured neighborhood of z. The exponent S is nonnegative:
`sum_indices_le_sum_distinct_orders` proves the required inequality.
If each a_j is nonzero, the limit is nonzero; hence the Wronskian is
nonzero sufficiently near z away from z.

The proof first establishes the limit of each scaled derivative

    (x-z)^i φ_j^(i)(x) / (x-z)^(r_j) → a_j (r_j).descFactorial(i).

For i ≤ r_j it uses Taylor's theorem and the lower vanishing derivatives.
For i > r_j it uses continuity multiplied by a positive power tending
to zero. This explicitly handles the case where naive natural subtraction
of exponents would lose information. Exact row and column scaling of the
determinant then gives the leading-term formula.

## Application to the rational family

The previously proved results give:
- independence of 1,f,x,xf,...,x^d,x^d f on the domain and as analytic germs;
- a constant coefficient basis with distinct first nonzero Taylor orders;
- the Wronskian change-of-basis identity, with nonzero basis determinant.

`eventually_rationalWronskian_ne_zero_of_not_rational` applies the new
formula to that basis and transfers the result back to the original family.
`exists_rationalWronskian_ne_zero_of_not_rational` provides a nonzero point
for every d, directly from analyticity and nonrationality.

Finally, `exists_escape_of_analytic_not_rational` applies the existing
counting and fusion construction with these Wronskians. For every nonempty
open V contained in the open preconnected analytic domain U, it gives
x in V and B ≥ 2 with Liouville x, PaperLiouville x,
EventualTargetAvoidance (f x) 100 B, and not Liouville (f x).
There is no extra derivative, counting or Wronskian hypothesis.

## Files and validation

New modules: WronskianLeadingTerm.lean and RationalWronskianNonvanishing.lean.
Both compiled with Lean 4.24.0 and warnings treated as errors.
All twelve new declarations were audited transitively: only propext,
Classical.choice and Quot.sound occur, without sorryAx.
The main import module and scripts/Audit.lean include these results.

The final irrationality-exponent statement is now `theorem_1_2` in
`IrrationalityExponent.lean`. See `THEOREM_1_2.md` for the complete statement
comparison and `../VALIDATION.md` for project verification results.
