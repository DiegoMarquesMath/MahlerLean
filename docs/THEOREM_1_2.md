# Legacy declaration \`theorem_1_2\`: single-point core of current Theorem 1.1

## Current manuscript numbering

The declaration \`MahlerLean.theorem_1_2\` predates the final manuscript
renumbering. It is the already verified **single-point quantitative core** of
the current Theorem 1.1 in

*Arithmetic Rigidity of Analytic Functions and Mahler's Problem on Liouville Numbers*.

The current manuscript strengthens this statement from one point \(\xi\) to a
Cantor set \(K\) of such points, with one common target-denominator cutoff.

## Lean declaration

\`MahlerLean.theorem_1_2\` in
\`MahlerLean/IrrationalityExponent.lean\` proves

\`\`\`text
∃ ξ ∈ V, Liouville ξ ∧ irrationalityExponent (f ξ) ≤ 100 ∧
  ∃ B : ℕ, 2 ≤ B ∧ EventualTargetAvoidance (f ξ) 100 B
\`\`\`

from openness and preconnectedness of \(U\), analyticity of \(f\) on \(U\),
nonrationality on \(U\), and \(V\) a nonempty open subset of \(U\).

There are no unproved counting, derivative, or Wronskian hypotheses.

## Statement correspondence

| Current manuscript single-point content | Lean | Correspondence |
| --- | --- | --- |
| \(U\) an open real interval | \`IsOpen U\`, \`IsPreconnected U\` | Every real interval is preconnected; nonemptiness follows from \(V\). |
| \(f\) real analytic on \(U\) | \`AnalyticOnNhd ℝ f U\` | Analytic at every point of the open domain. |
| \(f\) not rational on \(U\) | \`¬ IsRationalOn f U\` | No quotient of real polynomials with denominator nonzero on \(U\). |
| \(V\) a nonempty open subinterval of \(U\) | \`IsOpen V\`, \`V.Nonempty\`, \`V ⊆ U\` | Lean is slightly stronger: \(V\) need not itself be an interval. |
| \(\xi\) Liouville | mathlib \`Liouville ξ\` | \`liouville_iff_paperLiouville\` matches the paper's convention. |
| \(\mu(f(\xi))\le100\) | \`irrationalityExponent (f ξ) ≤ (100 : EReal)\` | Exact quantitative bound. |
| Eventual lower bound for all rational targets | \`EventualTargetAvoidance (f ξ) 100 B\` | Universal in every numerator and every denominator \(b\ge B\). |

Lean represents \(f\) as a total function \(\mathbb R\to\mathbb R\), but values
outside \(U\) are irrelevant and unrestricted.

## From target avoidance to the irrationality exponent

For every \(\lambda>100\),
\`approximationPairs_finite_of_eventual_target_avoidance\` proves finiteness of
the entire set of approximation pairs. Large denominators are excluded by the
eventual target-avoidance inequality. The finitely many small denominators admit
only finitely many numerators in the relevant approximation range. Hence no
\(\lambda>100\) contributes to the defining supremum, and therefore

\[
\mu(f(\xi))\le100.
\]

## Proof dependencies

The declaration composes:

- Proposition 5.1, the two-height counting estimate;
- source supply;
- infinite fusion;
- analytic derivative localization;
- rational-family independence;
- the adapted Taylor basis;
- the Wronskian leading-term argument;
- eventual target avoidance and the irrationality-exponent bridge.

The Wronskian criterion is documented in
[WRONSKIAN_CRITERION.md](WRONSKIAN_CRITERION.md), and Proposition 5.1 is
compared with the manuscript in [STEP14_PT.md](STEP14_PT.md).

## Cantor-set upgrade

The \`cantor-refinement\` branch upgrades this single-point theorem to the full
current Theorem 1.1. The arithmetic branchwise conclusions are already
formalized; the remaining task is the topological completion proving that the
limit set is perfect and totally disconnected.

The current Theorem 1.3 (entire-function rigidity) is formalized under the
legacy declaration name \`theorem_1_1\`; see
[THEOREM_1_1.md](THEOREM_1_1.md).

Reproducible build and audit results are recorded in
[VALIDATION.md](../VALIDATION.md).
