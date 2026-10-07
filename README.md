# Mahler's Problem on Liouville Numbers

[![Lean verification](https://github.com/DiegoMarquesMath/MahlerLean/actions/workflows/lean.yml/badge.svg?branch=cantor-refinement)](https://github.com/DiegoMarquesMath/MahlerLean/actions/workflows/lean.yml)

A Lean 4 formalization of the analytic-rigidity core of Diego Marques's
manuscript [*Arithmetic Rigidity of Analytic Functions and Mahler's Problem on Liouville Numbers*](paper/main.pdf).

> **Cantor refinement.** On the `cantor-refinement` branch, the local theorem is
> being upgraded from the already verified single-point escape statement to the
> full Cantor-set conclusion of the current Theorem 1.1. Until that upgrade is
> verified by CI, the claims below distinguish the verified core from the
> in-progress Cantor refinement.

## Main results

**Local quantitative rigidity (current Theorem 1.1).**

Let $U\subseteq\mathbb R$ be an open interval and let $f$ be real analytic
on $U$. Suppose that $f$ is not the restriction of a rational function
in $\mathbb R(x)$ without poles on $U$. The manuscript proves that every
nonempty open subinterval $V\subseteq U$ contains a Cantor set $K\subseteq
V$ of Liouville numbers such that

$$\mu(f(\xi))\leq 100 \qquad (\xi\in K).$$

Moreover, one cutoff $b_0$ works simultaneously on the whole Cantor set:

$$\left|f(\xi)-\frac{a}{b}\right|>b^{-100}$$

for every $\xi\in K$, every $a\in\mathbb Z$, and every integer
$b\ge b_0$.

The repository already verifies the corresponding single-point statement,
including the explicit eventual target-avoidance bound. The binary-tree
Cantor refinement is the remaining upgrade on this branch.

**Local rational rigidity (current Corollary 1.2).** If a real-analytic
$f:U\to\mathbb R$ maps every Liouville number in $U$ to a Liouville number,
then $f$ is the restriction of a rational function in $\mathbb R(x)$ with no
pole on $U$.

**Entire-function rigidity (current Theorem 1.3).** If an entire function
$F:\mathbb C\to\mathbb C$ maps every Liouville number to a Liouville number,
then $F$ is a polynomial with real coefficients. In particular, no
transcendental entire function has Maillet's property.

| Current manuscript result | Lean declaration | Source | Status |
| --- | --- | --- | --- |
| Theorem 1.1, single-point quantitative core | `MahlerLean.theorem_1_2` | [IrrationalityExponent.lean](MahlerLean/IrrationalityExponent.lean) | Verified |
| Theorem 1.1, Cantor-set refinement | forthcoming declaration on this branch | forthcoming Cantor module | In progress |
| Corollary 1.2 | `MahlerLean.rationalOn_of_preserves_liouville` | [EntireRigidity.lean](MahlerLean/EntireRigidity.lean) | Verified |
| Theorem 1.3 | `MahlerLean.theorem_1_1` (legacy declaration name) | [EntireRigidity.lean](MahlerLean/EntireRigidity.lean) | Verified |
| Proposition 5.1, uniform in the target cutoff | `MahlerLean.proposition_5_1` | [TwoHeightCounting.lean](MahlerLean/TwoHeightCounting.lean) | Verified |

The Lean declaration names `theorem_1_1` and `theorem_1_2` predate the
current manuscript renumbering. Compatibility aliases matching the final
paper numbering will be added with the Cantor refinement.

## Proof structure

The argument combines rational-point counting at independent source and
target heights with a fusion construction.

| Component | Role in the proof |
| --- | --- |
| Farey estimates | Supply rational source points with $c_F=1/4$ and bound their number in interval components. |
| Uniform analytic estimates | Control sublevel sets through Wronskians, jets and finite covers. |
| Two-height counting | Combine arithmetic and analytic determinants with multilinear perturbation bounds to prove Proposition 5.1. |
| Single-branch fusion | Construct a Liouville point whose image avoids sufficiently accurate rational approximations. |
| Binary fusion | Split every admissible successor into two separated children and obtain the Cantor set in Theorem 1.1. |
| Analytic nonrationality | Use independence, an adapted Taylor basis and the Wronskian leading term to discharge the analytic hypotheses. |
| Irrationality exponent | Deduce the bound $\mu(f(\xi))\le100$ from eventual target avoidance. |
| Entire-function rigidity | Combine Liouville density, real rational rigidity, the complex identity theorem and the fundamental theorem of algebra. |

See the [proof roadmap](docs/ROADMAP.md),
[declaration map](docs/FORMALIZATION.md), and
[guide in Portuguese](GUIA_PT.md).

## Verification

The existing single-point analytic-rigidity proof, Proposition 5.1, the
rational-rigidity corollary, and the entire-function theorem pass the local
build and axiom audit. The Cantor refinement is considered verified only
after the `cantor-refinement` branch passes the same GitHub Actions checks.

To reproduce the verification, install Lean following the
[Lean community guide](https://leanprover-community.github.io/get_started.html),
then run from the repository root:

```bash
lake exe cache get
bash scripts/check.sh
```

The project pins Lean 4.24.0 and mathlib v4.24.0. The script builds the
project, checks its source files with warnings treated as errors, and audits
the theorem axioms. GitHub Actions runs the same checks.

## Scope

The intended completed formalization covers Proposition 5.1, the full
current Theorem 1.1 including its Cantor-set strengthening, Corollary 1.2,
and Theorem 1.3. The independent Section 7 results remain outside this scope.

## Citation

After the Cantor refinement is verified, the manuscript may use:

```latex
A machine-checked Lean~4 formalization of Proposition~5.1 and of the complete
proof of Theorems~1.1 and~1.3, including the Cantor-set refinement in
Theorem~1.1, is available at
\url{https://github.com/DiegoMarquesMath/MahlerLean}.
```

For reproducibility, cite the exact verified commit used in the submitted
version.

Maintained by [Diego Marques](https://github.com/DiegoMarquesMath).
