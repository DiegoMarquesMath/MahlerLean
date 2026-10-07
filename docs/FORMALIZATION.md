# Formalized results

This document uses the **current manuscript numbering** of
*Arithmetic Rigidity of Analytic Functions and Mahler's Problem on Liouville Numbers*.

The Lean declaration names \`theorem_1_1\` and \`theorem_1_2\` were introduced
before the manuscript was renumbered. They are retained for compatibility:

- \`MahlerLean.theorem_1_2\` is the already verified **single-point quantitative core**
  of the current Theorem 1.1;
- \`MahlerLean.theorem_1_1\` is the current **Theorem 1.3** on entire-function rigidity.

The full Cantor-set strengthening of the current Theorem 1.1 is being completed
on the \`cantor-refinement\` branch.

## Principal entry points

| Declaration | Current manuscript role | Module |
| --- | --- | --- |
| \`proposition_5_1\` | Proposition 5.1: full two-height estimate, uniform in the target cutoff | TwoHeightCounting |
| \`proposition_5_1_uniformDangerBound\` | Counting input used by the fusion construction | TwoHeightCounting |
| \`liouville_iff_paperLiouville\` | Equivalence of the library and manuscript Liouville conventions | LiouvilleBridge |
| \`exists_escape_of_counting\` | Infinite fusion from explicit counting inputs | FusionEscape |
| \`exists_escape_of_analytic_wronskians\` | Discharges counting using Proposition 5.1 | FusionFromTwoHeight |
| \`exists_escape_in_open_of_analytic_wronskians\` | Derivative localization in every open subset | AnalyticDerivativeInterval |
| \`isRationalOn_of_polynomial_relation\` | Cancels apparent poles in an analytic rational relation | RationalRelation |
| \`rationalFamily_linearIndependent_of_not_rational\` | Independence of the indexed rational family | RationalFamilyIndependent |
| \`rationalFamily_exists_basis_distinct_orders\` | Adapted basis of analytic germs | RationalTaylorBasis |
| \`tendsto_wronskian_div_pow\` | Analytic Wronskian leading term | WronskianLeadingTerm |
| \`exists_rationalWronskian_ne_zero_of_not_rational\` | Discharges Wronskian nontriviality | RationalWronskianNonvanishing |
| \`exists_escape_of_analytic_not_rational\` | Single-point escape with exponent-100 target avoidance | RationalWronskianNonvanishing |
| \`irrationalityExponent_le_of_eventual_target_avoidance\` | Converts target avoidance into an irrationality-exponent bound | IrrationalityExponent |
| \`theorem_1_2\` | Single-point quantitative core of current Theorem 1.1 | IrrationalityExponent |
| \`rationalOn_of_preserves_liouville\` | Current Corollary 1.2: local rational rigidity | EntireRigidity |
| \`theorem_1_1\` | Current Theorem 1.3: entire-function rigidity | EntireRigidity |

Module links are relative to \`../MahlerLean/\`, with extension \`.lean\`.

The source-supply result uses \(c_F=1/4\). The two-height counting conclusion is

\[
C_{\mathrm{low}}Q^2H^{-98}+C(J,A)Q^{17/10},
\]

with the leading constant independent of the source subinterval and the lower
target cutoff, and with the remainder constant and threshold uniform in the
lower target cutoff.

## Current Theorem 1.1

The current manuscript strengthens the already verified single-point escape
statement to a Cantor-set statement: every nonempty open subinterval contains
a Cantor set \(K\) of Liouville numbers such that

\[
\mu(f(\xi))\le 100 \qquad (\xi\in K),
\]

with one common denominator cutoff for the whole set.

The \`cantor-refinement\` branch currently formalizes:

- binary successors from every admissible fusion stage;
- the full binary fusion tree and compact level sets;
- the compact limit set;
- the unique coherent branch through each limit-set point;
- Liouville approximation for every point of the limit set;
- one common target cutoff for the entire limit set;
- the bound \(\mu(f(\xi))\le100\) for every limit-set point;
- a subtree argument showing that every node interval meets the global limit set.

The remaining step is the topological completion: perfectness, total
disconnectedness, and final theorem-level assembly.

## Statement comparisons

- [Proposition 5.1](STEP14_PT.md): definitions, inherited hypotheses, exponents and quantifier order.
- [Legacy declaration \`theorem_1_2\`](THEOREM_1_2.md): single-point quantitative core of current Theorem 1.1.
- [Legacy declaration \`theorem_1_1\`](THEOREM_1_1.md): current Theorem 1.3, entire-function rigidity.
- [Wronskian criterion](WRONSKIAN_CRITERION.md): analytic leading term and removal of the last nontriviality assumption.

Historical \`STEP*.md\` files describe the scope at individual development
checkpoints; old lists of pending work in those files should be read historically.

## Scope

The intended completed analytic-rigidity formalization covers:

- Proposition 5.1;
- the full current Theorem 1.1, including the Cantor-set strengthening;
- Corollary 1.2;
- Theorem 1.3.

The independent Section 7 results — current Theorems 1.4 and 1.5 — remain
outside this formalization.

See [validation](../VALIDATION.md) for the actual build and axiom checks.
