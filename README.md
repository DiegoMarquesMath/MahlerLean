# Arithmetic Rigidity of Analytic Functions and Mahler's Problem on Liouville Numbers

[![Lean verification](https://github.com/DiegoMarquesMath/MahlerLean/actions/workflows/lean.yml/badge.svg?branch=cantor-refinement)](https://github.com/DiegoMarquesMath/MahlerLean/actions/workflows/lean.yml)

Lean 4 formalization of the analytic-rigidity core of Diego Marques's manuscript
[*Arithmetic Rigidity of Analytic Functions and Mahler's Problem on Liouville Numbers*](paper/main.pdf).

The formalization covers the two-height counting estimate, the full Cantor-set
version of the local rigidity theorem, the local rational-rigidity corollary,
and the entire-function consequence answering Mahler's problem.

## Verified results

### Theorem 1.1 — Local quantitative rigidity

Let $U\subseteq\mathbb R$ be an open interval and let $f:U\to\mathbb R$ be
real analytic. Suppose that $f$ is not the restriction to $U$ of a rational
function in $\mathbb R(x)$ without poles on $U$.

Then every nonempty open subinterval $V\subseteq U$ contains a nonempty compact,
perfect, totally disconnected set $K\subseteq V$ consisting of Liouville
numbers such that

$$
\mu(f(\xi))\le 100 \qquad (\xi\in K).
$$

Moreover, one cutoff $b_0\ge2$ works simultaneously for the whole set:

$$
\left|f(\xi)-\frac{a}{b}\right|>b^{-100}
$$

for every $\xi\in K$, every $a\in\mathbb Z$, and every integer $b\ge b_0$.

In the Lean development this is exposed as
[`MahlerLean.current_theorem_1_1`](MahlerLean/CurrentTheoremOne.lean).

### Corollary 1.2 — Local rational rigidity

If a real-analytic function $f:U\to\mathbb R$ satisfies

$$
f(\mathcal L\cap U)\subseteq\mathcal L,
$$

then $f$ is the restriction to $U$ of a rational function in
$\mathbb R(x)$ with no pole on $U$.

Lean declaration:
[`MahlerLean.current_corollary_1_2`](MahlerLean/CurrentTheoremOne.lean).

### Theorem 1.3 — Entire-function rigidity

If an entire function $F:\mathbb C\to\mathbb C$ satisfies

$$
F(\mathcal L)\subseteq\mathcal L,
$$

then $F\in\mathbb R[z]$. In particular, no transcendental entire function has
Maillet's property. This gives a negative answer, in the entire setting, to a
problem posed by Mahler in 1984.

Lean declaration:
[`MahlerLean.current_theorem_1_3`](MahlerLean/CurrentTheoremOne.lean).

### Proposition 5.1 — Two-height counting

The formalization includes the uniform two-height counting estimate on analytic
graphs, with source and target denominator scales treated independently and
uniformity in the lower target cutoff.

Lean declaration:
[`MahlerLean.proposition_5_1`](MahlerLean/TwoHeightCounting.lean).

## Correspondence with the Lean development

| Current manuscript result | Lean declaration | Source | Status |
| --- | --- | --- | --- |
| Proposition 5.1 | `MahlerLean.proposition_5_1` | [TwoHeightCounting.lean](MahlerLean/TwoHeightCounting.lean) | Verified |
| Theorem 1.1 — binary successor | `MahlerLean.exists_binary_fusion_transition` | [CantorFusion.lean](MahlerLean/CantorFusion.lean) | Verified |
| Theorem 1.1 — compact binary limit set | `MahlerLean.cantorLimitSet` | [CantorTree.lean](MahlerLean/CantorTree.lean) | Verified |
| Theorem 1.1 — branch arithmetic | `cantorLimitSet_liouville`, `cantorLimitSet_target_avoidance`, `cantorLimitSet_irrationalityExponent_le` | [CantorBranches.lean](MahlerLean/CantorBranches.lean) | Verified |
| Theorem 1.1 — every node meets the limit set | `MahlerLean.cantorLimitSet_meets_node` | [CantorSubtree.lean](MahlerLean/CantorSubtree.lean) | Verified |
| Theorem 1.1 — perfectness | `MahlerLean.cantorLimitSet_perfect` | [CantorTopology.lean](MahlerLean/CantorTopology.lean) | Verified |
| Theorem 1.1 — total disconnectedness | `MahlerLean.cantorLimitSet_isTotallyDisconnected` | [CantorTopology.lean](MahlerLean/CantorTopology.lean) | Verified |
| Theorem 1.1 — final assembly | `MahlerLean.current_theorem_1_1` | [CurrentTheoremOne.lean](MahlerLean/CurrentTheoremOne.lean) | Verified |
| Corollary 1.2 | `MahlerLean.current_corollary_1_2` | [CurrentTheoremOne.lean](MahlerLean/CurrentTheoremOne.lean) | Verified |
| Theorem 1.3 | `MahlerLean.current_theorem_1_3` | [CurrentTheoremOne.lean](MahlerLean/CurrentTheoremOne.lean) | Verified |

The older declarations `MahlerLean.theorem_1_1` and
`MahlerLean.theorem_1_2` predate the final manuscript renumbering and remain
available for compatibility. Under the current numbering, the former is
Theorem 1.3 and the latter is the single-point quantitative core of
Theorem 1.1.

## Cantor refinement

The Cantor-set strengthening is organized into five small modules:

- [CantorFusion.lean](MahlerLean/CantorFusion.lean): constructs two strictly
  separated admissible successors from each fusion stage;
- [CantorTree.lean](MahlerLean/CantorTree.lean): builds the binary tree, compact
  level sets, and the global limit set;
- [CantorBranches.lean](MahlerLean/CantorBranches.lean): extracts the coherent
  branch through each point and proves the Liouville and target-avoidance
  conclusions with one common root cutoff;
- [CantorSubtree.lean](MahlerLean/CantorSubtree.lean): proves that every node
  interval contains a point of the global limit set;
- [CantorTopology.lean](MahlerLean/CantorTopology.lean): proves uniform
  shrinking of the node intervals, perfectness, and total disconnectedness.

The final analytic assembly is in
[CurrentTheoremOne.lean](MahlerLean/CurrentTheoremOne.lean).

## Proof architecture

| Component | Role |
| --- | --- |
| Farey estimates | Supply reduced rational source points and control their number in unions of intervals. |
| Uniform analytic sublevel estimates | Control normalized target-linear relations through Wronskians, jets, and finite covers. |
| Two-height counting | Combine analytic and arithmetic determinant bounds at independent source and target heights. |
| Single-branch fusion | Produce Liouville source approximation together with eventual target avoidance. |
| Binary fusion | Run the safe-center construction simultaneously along a full binary tree. |
| Cantor topology | Prove shrinking diameters, perfectness, and total disconnectedness. |
| Entire-function rigidity | Combine local rational rigidity, Liouville density, analytic continuation, and absence of poles. |

## Verification

The complete build and the listed-theorem audit pass on Lean 4.24.0 and
mathlib v4.24.0.

To reproduce the verification:

```bash
lake exe cache get
bash scripts/check.sh
```

The verification script:

1. builds the complete project;
2. checks every project source with warnings treated as errors;
3. prints the axioms of the listed principal declarations;
4. fails if any listed theorem depends on `sorryAx`.

Verified proof commit:

[`dcbac6a16e910c22155e4882a3b11b2bb0c66222`](https://github.com/DiegoMarquesMath/MahlerLean/tree/dcbac6a16e910c22155e4882a3b11b2bb0c66222)

## Scope

The completed formalization covers Proposition 5.1, Theorem 1.1,
Corollary 1.2, and Theorem 1.3 of the current manuscript.

The independent Section 7 results — Theorems 1.4 and 1.5 — are not part of
the present Lean project.

## Citation

Suggested manuscript wording:

> A machine-checked Lean 4 formalization of Proposition 5.1 and of the complete
> proof of Theorems 1.1 and 1.3, including the Cantor-set refinement in
> Theorem 1.1, is available in the
> [MahlerLean repository](https://github.com/DiegoMarquesMath/MahlerLean).

For reproducibility, the submitted version should cite the exact verified
commit above.

Maintained by [Diego Marques](https://github.com/DiegoMarquesMath).
