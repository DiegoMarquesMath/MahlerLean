# Formalized results

The principal entry points are Proposition 5.1 and the local quantitative
Theorem 1.2. All intermediate hypotheses of the counting and fusion
interfaces are discharged when proving `theorem_1_2`.

| Declaration | Mathematical role | Module |
| --- | --- | --- |
| `proposition_5_1` | Full two-height estimate, uniform in target cutoff H | TwoHeightCounting |
| `proposition_5_1_uniformDangerBound` | Supplies the counting input to fusion | TwoHeightCounting |
| `liouville_iff_paperLiouville` | Equivalence of the library and manuscript Liouville conventions | LiouvilleBridge |
| `exists_escape_of_counting` | Infinite fusion from explicit counting inputs | FusionEscape |
| `exists_escape_of_analytic_wronskians` | Discharges counting using Proposition 5.1 | FusionFromTwoHeight |
| `exists_escape_in_open_of_analytic_wronskians` | Derivative localization in every open subset | AnalyticDerivativeInterval |
| `isRationalOn_of_polynomial_relation` | Cancels apparent poles in an analytic rational relation | RationalRelation |
| `rationalFamily_linearIndependent_of_not_rational` | Independence of the exact indexed rational family | RationalFamilyIndependent |
| `rationalFamily_exists_basis_distinct_orders` | Constant adapted basis of analytic germs | RationalTaylorBasis |
| `tendsto_wronskian_div_pow` | Analytic Wronskian leading term with exponent sum(r_j)-N(N-1)/2 | WronskianLeadingTerm |
| `exists_rationalWronskian_ne_zero_of_not_rational` | Discharges Wronskian nontriviality | RationalWronskianNonvanishing |
| `exists_escape_of_analytic_not_rational` | Escape with exponent-100 target avoidance from original hypotheses | RationalWronskianNonvanishing |
| `irrationalityExponent_le_of_eventual_target_avoidance` | Converts avoidance into the extended-real supremum bound | IrrationalityExponent |
| `theorem_1_2` | ξ ∈ V Liouville and μ(f(ξ)) ≤ 100, with eventual strict avoidance | IrrationalityExponent |

Module links are relative to `../MahlerLean/`, with extension `.lean`.
The source supply result uses cF = 1/4. The counting conclusion is
C_low Q² H^(-98) + C Q^(17/10). The leading constant precedes J and A;
the remainder constant and threshold precede H.

## Statement comparisons

- [Proposition 5.1](STEP14_PT.md): definitions, inherited hypotheses, exponents and quantifier order.
- [Theorem 1.2](THEOREM_1_2.md): domain, rationality, Liouville convention, irrationality exponent and eventual bound.
- [Wronskian criterion](WRONSKIAN_CRITERION.md): analytic leading term and removal of the last nontriviality assumption.

The older `FusionInputs` and related conditional interfaces remain useful
intermediate theorems. Their presence does not introduce extra assumptions
into the final theorem. Historical `STEP*.md` files describe the scope at
each development checkpoint; their old lists of pending work are historical.

Theorem 1.1 and the independent Section 7 results are outside this completed
formalization scope. See [validation](../VALIDATION.md) for the actual checks.
