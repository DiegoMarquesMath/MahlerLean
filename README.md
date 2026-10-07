# Arithmetic Rigidity of Analytic Functions and Mahler's Problem on Liouville Numbers

[![Lean verification](https://github.com/DiegoMarquesMath/MahlerLean/actions/workflows/lean.yml/badge.svg?branch=main)](https://github.com/DiegoMarquesMath/MahlerLean/actions/workflows/lean.yml)

Lean 4 formalization of the analytic-rigidity core of Diego Marques's manuscript
[*Arithmetic Rigidity of Analytic Functions and Mahler's Problem on Liouville Numbers*](paper/main.pdf).

The current manuscript proves a local quantitative rigidity theorem for real-analytic
functions, derives a negative solution to Mahler's 1984 problem for entire functions,
and then studies coefficient rigidity and nonlinear sharpness for rational maps.

> **Current formalization status.**
> The `main` branch verifies the single-point quantitative core of the current
> Theorem 1.1, Corollary 1.2, Theorem 1.3, and Proposition 5.1.
> The full Cantor-set strengthening in Theorem 1.1 is being formalized on the
> [`cantor-refinement`](../../tree/cantor-refinement) branch.

## Main results

### Theorem 1.1 — Local quantitative rigidity

Let $U\subseteq\mathbb R$ be an open interval and let $f:U\to\mathbb R$
be real analytic. Suppose that $f$ is not the restriction to $U$ of a
rational function in $\mathbb R(x)$ without poles on $U$.

Then every nonempty open subinterval $V\subseteq U$ contains a Cantor set
$K\subseteq V$ of Liouville numbers such that

$
\mu(f(\xi))\le 100 \qquad (\xi\in K).
$

More precisely, one cutoff $b_0\ge 2$ may be chosen so that

$
\left|f(\xi)-\frac{a}{b}\right|>b^{-100}
$

for every $\xi\in K$, every $a\in\mathbb Z$, and every integer $b\ge b_0$.

The `main` branch currently verifies the corresponding single-point statement,
including the explicit eventual target-avoidance bound. The binary-tree Cantor
refinement is the remaining topological upgrade.

### Corollary 1.2 — Local rational rigidity

If a real-analytic function $f:U\to\mathbb R$ satisfies

$
f(\mathcal L\cap U)\subseteq \mathcal L,
$

then $f$ is the restriction to $U$ of a rational function in
$\mathbb R(x)$ with no pole on $U$.

### Theorem 1.3 — Entire-function rigidity

If an entire function $F:\mathbb C\to\mathbb C$ satisfies

$
F(\mathcal L)\subseteq \mathcal L,
$

then $F\in\mathbb R[z]$. In particular, no transcendental entire function
has Maillet's property.

This gives a negative answer, in the entire setting, to a problem posed by
Mahler in 1984.

### Proposition 5.1 — Two-height counting

The formalization includes the uniform two-height counting estimate on analytic
graphs, with source and target denominator scales treated independently and
uniformity in the lower target cutoff.

## Correspondence with the Lean development

| Current manuscript result | Lean declaration | Source | Status |
| --- | --- | --- | --- |
| Theorem 1.1, single-point quantitative core | `MahlerLean.theorem_1_2` | [IrrationalityExponent.lean](MahlerLean/IrrationalityExponent.lean) | Verified |
| Theorem 1.1, Cantor-set strengthening | branch `cantor-refinement` | `CantorFusion.lean`, `CantorTree.lean`, `CantorBranches.lean`, `CantorSubtree.lean` | In progress |
| Corollary 1.2 | `MahlerLean.rationalOn_of_preserves_liouville` | [EntireRigidity.lean](MahlerLean/EntireRigidity.lean) | Verified |
| Theorem 1.3 | `MahlerLean.theorem_1_1` | [EntireRigidity.lean](MahlerLean/EntireRigidity.lean) | Verified |
| Proposition 5.1 | `MahlerLean.proposition_5_1` | [TwoHeightCounting.lean](MahlerLean/TwoHeightCounting.lean) | Verified |

The declaration names `theorem_1_1` and `theorem_1_2` predate the current
manuscript renumbering. Compatibility aliases matching the final paper numbering
will be added together with the completed Cantor refinement.

## Additional manuscript results

The current manuscript also contains two independent Section 7 results:

- **Theorem 1.4 (Möbius rigidity).** A real Möbius transformation has Maillet's
  property if and only if it belongs to $\mathbb Q(x)$.
- **Theorem 1.5 (nonlinear sharpness).** There exist continuum many positive
  transcendental real numbers $\sigma$ such that
  $\sigma\xi^m\in\mathcal L$ for every $\xi\in\mathcal L$ and every
  integer $m\ge 2$.

These Section 7 results are mathematically independent of the analytic
two-height argument and are currently outside the scope of this Lean project.

## Proof structure

| Component | Role in the proof |
| --- | --- |
| Farey estimates | Supply reduced rational source points and control their number in unions of intervals. |
| Uniform analytic estimates | Control sublevel sets through Wronskians, jets and finite covers. |
| Two-height counting | Combine analytic and arithmetic determinant bounds to prove Proposition 5.1. |
| Single-branch fusion | Construct one Liouville point whose image avoids very good rational approximations. |
| Binary fusion | Upgrade the construction to a Cantor family of such points. |
| Analytic nonrationality | Discharge the Wronskian hypotheses from analyticity and nonrationality. |
| Irrationality exponent | Deduce the uniform bound $\mu(f(\xi))\le100$ from eventual target avoidance. |
| Entire-function rigidity | Combine local rational rigidity, Liouville density, analytic continuation and the absence of poles. |

See the [proof roadmap](docs/ROADMAP.md),
[declaration map](docs/FORMALIZATION.md), and
[guide in Portuguese](GUIA_PT.md).

## Verification

The current `main` branch passes the complete build and axiom audit for the
verified statements listed above.

To reproduce the verification:

```bash
lake exe cache get
bash scripts/check.sh
```

The project pins Lean 4.24.0 and its dependencies. GitHub Actions runs the same
checks.

## Scope

The intended completed formalization covers:

- Proposition 5.1;
- the full current Theorem 1.1, including its Cantor-set strengthening;
- Corollary 1.2;
- Theorem 1.3.

The independent Section 7 results, including Theorems 1.4 and 1.5, remain
outside the present formalization.

## Citation

Once the Cantor refinement is fully verified, the manuscript may use:

```latex
A machine-checked Lean~4 formalization of Proposition~5.1 and of the complete
proof of Theorems~1.1 and~1.3, including the Cantor-set refinement in
Theorem~1.1, is available at
\url{https://github.com/DiegoMarquesMath/MahlerLean}.
```

For reproducibility, cite the exact verified commit used in the submitted
version.

Maintained by [Diego Marques](https://github.com/DiegoMarquesMath).
