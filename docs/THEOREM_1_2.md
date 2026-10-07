# Legacy declaration `theorem_1_2`: single-point core of current Theorem 1.1

## Current manuscript numbering

The declaration `MahlerLean.theorem_1_2` predates the final manuscript
renumbering. It is the verified **single-point quantitative core** of the
current Theorem 1.1.

The full current theorem is now formalized as
`MahlerLean.current_theorem_1_1` in
[CurrentTheoremOne.lean](../MahlerLean/CurrentTheoremOne.lean).

## Legacy Lean declaration

`MahlerLean.theorem_1_2` in
[IrrationalityExponent.lean](../MahlerLean/IrrationalityExponent.lean) proves

```text
∃ ξ ∈ V, Liouville ξ ∧ irrationalityExponent (f ξ) ≤ 100 ∧
  ∃ B : ℕ, 2 ≤ B ∧ EventualTargetAvoidance (f ξ) 100 B
```

from openness and preconnectedness of $U$, analyticity of $f$ on $U$,
nonrationality on $U$, and $V$ a nonempty open subset of $U$.

There are no unproved counting, derivative, or Wronskian hypotheses.

## Statement correspondence

| Manuscript content | Lean |
| --- | --- |
| $U$ an open real interval | `IsOpen U`, `IsPreconnected U` |
| $f$ real analytic on $U$ | `AnalyticOnNhd ℝ f U` |
| $f$ not rational on $U$ | `¬ IsRationalOn f U` |
| $V$ nonempty and open in $U$ | `IsOpen V`, `V.Nonempty`, `V ⊆ U` |
| $\xi$ Liouville | mathlib `Liouville ξ` |
| $\mu(f(\xi))\le100$ | `irrationalityExponent (f ξ) ≤ (100 : EReal)` |
| Uniform eventual lower bound | `EventualTargetAvoidance (f ξ) 100 B` |

The Lean statement is slightly stronger in that $V$ need not itself be an
interval.

## Cantor-set upgrade

The completed binary refinement upgrades the single-point theorem to a
nonempty compact perfect totally disconnected set $K$, with one common target
cutoff and

$$
\mu(f(\xi))\le100 \qquad (\xi\in K).
$$

The construction is documented in
[CANTOR_REFINEMENT.md](CANTOR_REFINEMENT.md) and assembled in
[CurrentTheoremOne.lean](../MahlerLean/CurrentTheoremOne.lean).

The current Theorem 1.3 is available under the numbering-stable alias
`MahlerLean.current_theorem_1_3`.
