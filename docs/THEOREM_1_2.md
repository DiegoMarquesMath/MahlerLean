# Theorem 1.2: statement correspondence and verification

Reference manuscript: `paper/main.tex` at commit
`d168565513791c9ad3348dd4fdd6a358c87a233d`, labels `eq:intro-mu` and
`thm:intro-local`. The source was read alongside the final Lean declarations.
This is a mathematical comparison of statements; Lean checks the formal
statement, not the LaTeX document itself.

## Final declaration

`MahlerLean.theorem_1_2` in `MahlerLean/IrrationalityExponent.lean` gives

    ∃ ξ ∈ V, Liouville ξ ∧ irrationalityExponent (f ξ) ≤ 100 ∧
      ∃ B : ℕ, 2 ≤ B ∧ EventualTargetAvoidance (f ξ) 100 B

from openness and preconnectedness of U, analyticity of f on U,
nonrationality on U, and V a nonempty open subset of U.
There are no unproved counting, derivative or Wronskian hypotheses.
The constant 100 is fixed independently of f, U and V and is greater than 2.

| Manuscript | Lean | Correspondence |
| --- | --- | --- |
| U an open real interval | `IsOpen U`, `IsPreconnected U` | Every real interval is preconnected; nonemptiness follows from V. |
| f real analytic on U | `AnalyticOnNhd ℝ f U` | At every point of the open domain. |
| f not a restriction of a rational function without poles on U | `¬ IsRationalOn f U` | A quotient of real polynomials with denominator nonzero everywhere on U. |
| V a nonempty open subinterval of U | `IsOpen V`, `V.Nonempty`, `V ⊆ U` | The Lean result is stronger: V need not itself be an interval. |
| ξ Liouville | mathlib `Liouville ξ` | `liouville_iff_paperLiouville` proves agreement with the paper's infinitely-many-pairs convention. |
| Positive exponents λ and infinitely many (a,b) ∈ ℤ × ℤ_{>0} | `approximationPairs y lam` with `0 < p.2` | Positive integers represented by naturals; no reduced-fraction condition. |
| 0 < abs(y-a/b) < b^(-λ) | The two strict inequalities in `approximationPairs` | Zero errors are excluded exactly as in the paper. |
| μ as a supremum, allowing +∞ | `irrationalityExponent : ℝ → EReal` | Supremum of the same set of positive real exponents, embedded in extended reals. |
| μ(f(ξ)) ≤ 100 | `irrationalityExponent (f ξ) ≤ (100 : EReal)` | Exact quantitative bound. |
| abs(f(ξ)-a/b) > b^(-100) for all a and sufficiently large b | `∃ B, 2 ≤ B ∧ EventualTargetAvoidance (f ξ) 100 B` | Universal in numerator a and all b ≥ B; inverse natural powers agree with negative real powers. |

Lean represents f as a total function ℝ → ℝ. Values outside U are unrestricted.
A function defined only on U can be extended arbitrarily outside that open
set without changing its analytic germs on U. No global analyticity is assumed.

## From avoidance to the supremum bound

For every lam > tau, `approximationPairs_finite_of_eventual_target_avoidance`
proves finiteness of the entire set of pairs, not merely finiteness of the
denominator set. All sufficiently large b are excluded by monotonicity of
b^(-lam). For the remaining positive b < B, the error is less than 1, so
abs(a) < b(abs(y)+1) ≤ B(abs(y)+1). The pairs therefore lie in an explicit
finite integer/natural rectangle. Consequently every exponent contributing
to the supremum is at most tau.

## Proof dependencies and scope

The final theorem composes the two-height estimate of Proposition 5.1,
source supply, infinite fusion, analytic derivative localization, rational
family independence, the adapted Taylor basis and the Wronskian leading-term
formula. The Wronskian criterion is documented in `WRONSKIAN_CRITERION.md`;
Proposition 5.1's statement comparison is in `STEP14_PT.md`.

This completes the local quantitative statement of Theorem 1.2.
The entire-function consequence, Theorem 1.1, is now formalized in
`EntireRigidity.lean`; see [THEOREM_1_1.md](THEOREM_1_1.md).
The independent Section 7 statements remain outside the formalization scope.
Reproducible build and audit results are recorded in `../VALIDATION.md`.
