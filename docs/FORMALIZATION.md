# Formalized results

This document uses the **current manuscript numbering** of
*Arithmetic Rigidity of Analytic Functions and Mahler's Problem on Liouville Numbers*.

The older Lean declaration names `theorem_1_1` and `theorem_1_2` predate the
final manuscript renumbering and remain available for compatibility:

- `MahlerLean.theorem_1_2` is the single-point quantitative core of the current
  Theorem 1.1;
- `MahlerLean.theorem_1_1` is the current Theorem 1.3 on entire-function
  rigidity.

Numbering-stable declarations are now provided by
`MahlerLean/CurrentTheoremOne.lean`.

## Principal entry points

| Declaration | Current manuscript role | Module |
| --- | --- | --- |
| `proposition_5_1` | Proposition 5.1: two-height estimate, uniform in the lower target cutoff | `TwoHeightCounting` |
| `exists_escape_of_analytic_not_rational` | Single-point quantitative escape from the original analytic hypotheses | `RationalWronskianNonvanishing` |
| `irrationalityExponent_le_of_eventual_target_avoidance` | Converts target avoidance into an irrationality-exponent bound | `IrrationalityExponent` |
| `exists_binary_fusion_transition` | Two separated successors from every admissible fusion stage | `CantorFusion` |
| `cantorLimitSet` | Compact binary limit set | `CantorTree` |
| `cantorLimitSet_liouville` | Every point of the limit set is Liouville | `CantorBranches` |
| `cantorLimitSet_target_avoidance` | One common root cutoff works on the whole limit set | `CantorBranches` |
| `cantorLimitSet_irrationalityExponent_le` | Image irrationality exponent at most 100 on the whole limit set | `CantorBranches` |
| `cantorLimitSet_meets_node` | Every node interval meets the global limit set | `CantorSubtree` |
| `cantorLimitSet_perfect` | Perfectness of the limit set | `CantorTopology` |
| `cantorLimitSet_isTotallyDisconnected` | Total disconnectedness of the limit set | `CantorTopology` |
| `current_theorem_1_1` | Full current Theorem 1.1 | `CurrentTheoremOne` |
| `current_corollary_1_2` | Current Corollary 1.2 | `CurrentTheoremOne` |
| `current_theorem_1_3` | Current Theorem 1.3 | `CurrentTheoremOne` |

The two-height counting conclusion has the form

$$
C_{\mathrm{low}}Q^2H^{-98}+C(J,A)Q^{17/10},
$$

with the leading constant independent of the source subinterval and the lower
target cutoff, and with the remainder constant and threshold uniform in the
lower target cutoff.

## Current Theorem 1.1

The completed formalization constructs, inside every prescribed nonempty open
subinterval, a nonempty compact perfect totally disconnected set $K$ such that
every $\xi\in K$ is Liouville and

$$
\mu(f(\xi))\le100.
$$

A single denominator cutoff works simultaneously for every point of $K$.

The Cantor proof is split into:

- [CantorFusion.lean](../MahlerLean/CantorFusion.lean);
- [CantorTree.lean](../MahlerLean/CantorTree.lean);
- [CantorBranches.lean](../MahlerLean/CantorBranches.lean);
- [CantorSubtree.lean](../MahlerLean/CantorSubtree.lean);
- [CantorTopology.lean](../MahlerLean/CantorTopology.lean);
- [CurrentTheoremOne.lean](../MahlerLean/CurrentTheoremOne.lean).

See [CANTOR_REFINEMENT.md](CANTOR_REFINEMENT.md) for the detailed decomposition.

## Verification and scope

The complete build, warning-as-error source checks, and listed-theorem
placeholder audit pass on Lean 4.24.0 and mathlib v4.24.0.

The completed analytic-rigidity formalization covers:

- Proposition 5.1;
- the full current Theorem 1.1, including the Cantor-set strengthening;
- Corollary 1.2;
- Theorem 1.3.

The independent Section 7 results — current Theorems 1.4 and 1.5 — remain
outside this formalization.

Historical `STEP*.md` files record intermediate development checkpoints and
should be read as historical notes.
