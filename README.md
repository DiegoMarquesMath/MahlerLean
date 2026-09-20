# Mahler's Question on Liouville Numbers

[![Lean verification](https://github.com/DiegoMarquesMath/MahlerLean/actions/workflows/lean.yml/badge.svg?branch=main)](https://github.com/DiegoMarquesMath/MahlerLean/actions/workflows/lean.yml)

A Lean 4 formalization accompanying Diego Marques's manuscript
[*Mahler's problem on Liouville numbers*](paper/main.pdf).

**The local quantitative Theorem 1.2 and the two-height counting estimate
of Proposition 5.1 are formalized.** The final theorem includes the
irrationality-exponent bound and has no additional counting, derivative
or Wronskian hypotheses.

**Project URL:** [github.com/DiegoMarquesMath/MahlerLean](https://github.com/DiegoMarquesMath/MahlerLean)

| Result | Lean declaration | Source |
| --- | --- | --- |
| Theorem 1.2, including $\mu(f(\xi))\le100$ | `MahlerLean.theorem_1_2` | [IrrationalityExponent.lean](MahlerLean/IrrationalityExponent.lean) |
| Proposition 5.1, uniform in the target cutoff | `MahlerLean.proposition_5_1` | [TwoHeightCounting.lean](MahlerLean/TwoHeightCounting.lean) |

[Main theorem](MahlerLean/IrrationalityExponent.lean) ·
[Manuscript](paper/main.pdf) ·
[Statement comparison](docs/THEOREM_1_2.md) ·
[Validation](VALIDATION.md) ·
[Guia em português](GUIA_PT.md)

## Main result

Let $U\subseteq\mathbb R$ be an open interval and let $f$ be real analytic
on $U$. Suppose that $f$ is not the restriction of a rational function
in $\mathbb R(x)$ without poles on $U$. Then every nonempty open
subinterval $V\subseteq U$ contains a Liouville number $\xi$ such that

$$\mu(f(\xi))\leq 100.$$

In fact, for every integer $a$ and every sufficiently large positive
integer $b$,

$$\left|f(\xi)-\frac{a}{b}\right|>b^{-100}.$$

The declaration [`MahlerLean.theorem_1_2`](MahlerLean/IrrationalityExponent.lean)
proves this statement. The irrationality exponent is the extended-real
supremum defined using infinitely many integer numerator/positive
denominator pairs, with strictly positive approximation error, as in
the manuscript. The Lean statement allows any nonempty open subset $V$.

## Proof structure

The argument combines rational point counting at independent source and
target heights with a nested-interval construction.

| Component | Formalization |
| --- | --- |
| Farey source supply and rational packing | Source supply with $c_F=1/4$; separation and interval-component upper bounds. |
| Uniform analytic estimates | Wronskians, jets, finite covers and sublevel estimates. |
| Proposition 5.1 | Arithmetic and analytic determinants, multilinear perturbations, and complete small/large target-block counting, uniform in the target cutoff. |
| Infinite fusion | Safe centers and nested intervals yield a Liouville point with eventual target avoidance. |
| Analytic nonrationality | Independence, an adapted Taylor basis and the Wronskian leading term discharge the analytic hypotheses of fusion. |
| Theorem 1.2 | The resulting image has irrationality exponent at most 100. |

See the [proof roadmap](docs/ROADMAP.md),
[declaration map](docs/FORMALIZATION.md), and
[Proposition 5.1 comparison](docs/STEP14_PT.md).
The conditional interfaces in intermediate modules are instantiated in
the final theorem. Historical development notes record earlier checkpoints.

## Verification record

The complete local verification at
[commit `babdfb8`](https://github.com/DiegoMarquesMath/MahlerLean/tree/babdfb81675dbce78991bef3cd8e9a4350635e1f)
passed with Lean 4.24.0: all 88 project modules checked with warnings as
errors and all 352 listed declarations audited. The only reported axioms
were `propext`, `Classical.choice` and `Quot.sound`, with no `sorryAx`.
The [GitHub Actions run for that exact proof commit](https://github.com/DiegoMarquesMath/MahlerLean/actions/runs/35528475325)
provides its separate remote verification status.

## Reproduce the verification

Install Lean using the [Lean community guide](https://leanprover-community.github.io/get_started.html).
From the repository root, run:

```bash
lake exe cache get
bash scripts/check.sh
```

The project pins Lean 4.24.0 and its dependencies in `lean-toolchain` and
`lake-manifest.json`. The script builds the project, checks every project
source with warnings treated as errors, and audits the listed theorem
axioms, rejecting `sorryAx`. The [GitHub workflow](https://github.com/DiegoMarquesMath/MahlerLean/actions/workflows/lean.yml)
runs the same checks. Actual verification results are recorded in
[VALIDATION.md](VALIDATION.md).

## Scope and citation

This formalization covers Proposition 5.1 and the local quantitative
Theorem 1.2. It does not claim that every result in the manuscript is
formalized; the entire-function consequence of Theorem 1.1 and the
independent Section 7 results are outside this scope. The general
finite-smoothness version of the sublevel theorem is not claimed.

The kernel verifies the Lean statements. The correspondence to the
manuscript is documented separately in the statement comparisons.
A concise statement for the manuscript is:

> A formalization of Theorem 1.2 in the Lean 4 proof assistant is available at https://github.com/DiegoMarquesMath/MahlerLean.

```latex
A formalization of Theorem~1.2 in the Lean~4 proof assistant is
available at \url{https://github.com/DiegoMarquesMath/MahlerLean}.
```

For a version-specific reference, cite the proof commit
[`babdfb81675dbce78991bef3cd8e9a4350635e1f`](https://github.com/DiegoMarquesMath/MahlerLean/tree/babdfb81675dbce78991bef3cd8e9a4350635e1f).
This pins the statements and proofs independently of later documentation changes.

Maintained by [Diego Marques](https://github.com/DiegoMarquesMath).
