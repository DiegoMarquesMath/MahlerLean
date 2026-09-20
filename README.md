# Mahler's Problem on Liouville Numbers

[![Lean verification](https://github.com/DiegoMarquesMath/MahlerLean/actions/workflows/lean.yml/badge.svg?branch=main)](https://github.com/DiegoMarquesMath/MahlerLean/actions/workflows/lean.yml)

A Lean 4 formalization of Theorems 1.1 and 1.2 and the two-height
counting estimate of Proposition 5.1 in Diego Marques's
manuscript [*Mahler's Problem on Liouville Numbers*](paper/main.pdf).

## Main results

**Entire-function rigidity (Theorem 1.1).** If an entire function
$F:\mathbb C\to\mathbb C$ maps every Liouville number to a Liouville number,
then $F$ is a polynomial with real coefficients. In particular, no
transcendental entire function has this property.

**Local quantitative theorem (Theorem 1.2).**

Let $U\subseteq\mathbb R$ be an open interval and let $f$ be real analytic
on $U$. Suppose that $f$ is not the restriction of a rational function
in $\mathbb R(x)$ without poles on $U$. Then every nonempty open
subinterval $V\subseteq U$ contains a Liouville number $\xi$ such that

$$\mu(f(\xi))\leq 100.$$

In fact, for every integer $a$ and every sufficiently large positive
integer $b$,

$$\left|f(\xi)-\frac{a}{b}\right|>b^{-100}.$$

The final theorem proves this conclusion from analyticity and
nonrationality, with no additional counting, derivative or Wronskian
hypotheses.

| Result | Lean declaration | Source |
| --- | --- | --- |
| Theorem 1.1 | `MahlerLean.theorem_1_1` | [EntireRigidity.lean](MahlerLean/EntireRigidity.lean) |
| Theorem 1.2 | `MahlerLean.theorem_1_2` | [IrrationalityExponent.lean](MahlerLean/IrrationalityExponent.lean) |
| Proposition 5.1, uniform in the target cutoff | `MahlerLean.proposition_5_1` | [TwoHeightCounting.lean](MahlerLean/TwoHeightCounting.lean) |

The comparisons for [Theorem 1.1](docs/THEOREM_1_1.md), [Theorem 1.2](docs/THEOREM_1_2.md) and
[Proposition 5.1](docs/STEP14_PT.md) document the correspondence between
the manuscript and the formal statements, including definitions and hypotheses.

## Proof structure

The argument combines rational point counting at independent source and
target heights with a nested-interval construction.

| Component | Role in the proof |
| --- | --- |
| Farey estimates | Supply rational source points with $c_F=1/4$ and bound their number in interval components. |
| Uniform analytic estimates | Control sublevel sets through Wronskians, jets and finite covers. |
| Two-height counting | Combine arithmetic and analytic determinants with multilinear perturbation bounds to prove Proposition 5.1. |
| Infinite fusion | Construct a Liouville point whose image avoids sufficiently accurate rational approximations. |
| Analytic nonrationality | Use independence, an adapted Taylor basis and the Wronskian leading term to discharge the analytic hypotheses. |
| Irrationality exponent | Deduce the bound $\mu(f(\xi))\le100$ from eventual target avoidance. |
| Entire-function rigidity | Combine Liouville density, real rational rigidity, the complex identity theorem and the fundamental theorem of algebra. |

See the [proof roadmap](docs/ROADMAP.md),
[declaration map](docs/FORMALIZATION.md), and
[guide in Portuguese](GUIA_PT.md).

## Verification

The complete local build and axiom audit passed, including Theorem 1.1.
The [validation record](VALIDATION.md) contains the detailed results and
links to remote checks.

To reproduce the verification, install Lean following the
[Lean community guide](https://leanprover-community.github.io/get_started.html),
then run from the repository root:

```bash
lake exe cache get
bash scripts/check.sh
```

The project pins Lean 4.24.0 and its dependencies. The script builds the
project, checks its source files with warnings treated as errors, and audits
the theorem axioms. GitHub Actions runs the same checks.

## Scope

The formalization covers Theorems 1.1 and 1.2, Proposition 5.1, and the
real-analytic rational-rigidity corollary used in the entire case.
The independent Section 7 results and the general finite-smoothness version
of the sublevel theorem are outside this scope.

## Citation

The following sentence can be used in the manuscript:

```latex
A formalization of Theorems~1.1 and~1.2 in the Lean~4 proof assistant is
available at \url{https://github.com/DiegoMarquesMath/MahlerLean}.
```

For reproducibility, include the exact commit used. The earlier
[proof commit `babdfb8`](https://github.com/DiegoMarquesMath/MahlerLean/tree/babdfb81675dbce78991bef3cd8e9a4350635e1f)
covers Theorem 1.2 and Proposition 5.1; Theorem 1.1 is added in the commit
introducing [EntireRigidity.lean](MahlerLean/EntireRigidity.lean).

Maintained by [Diego Marques](https://github.com/DiegoMarquesMath).
