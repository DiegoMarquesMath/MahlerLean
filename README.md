# Mahler's Question on Liouville Numbers

[![Lean verification](https://github.com/DiegoMarquesMath/MahlerLean/actions/workflows/lean.yml/badge.svg?branch=step13-determinants)](https://github.com/DiegoMarquesMath/MahlerLean/actions/workflows/lean.yml?query=branch%3Astep13-determinants)

A Lean 4 formalization project accompanying Diego Marques's manuscript
[*Mahler's problem on Liouville numbers*](paper/main.pdf).
The current focus is the counting estimate in Proposition 5.1 and the
Liouville escape theorem, Theorem 1.2.

Mahler asked whether a transcendental entire function could map every
Liouville number to a Liouville number. The manuscript addresses this
question through the following local statement, which is the principal
target of this formalization:

> Let $U\subseteq\mathbb R$ be a nonempty open interval, and let
> $f:U\to\mathbb R$ be real analytic and not the restriction of a rational
> function in $\mathbb R(x)$ without poles on $U$. Every nonempty open subinterval $V\subseteq U$
> contains a Liouville number $\xi$ such that $\mu(f(\xi))\leq 100$.

Here $\mu$ denotes the irrationality exponent. The proof combines rational
point counting at independent source and target heights, Wronskian
estimates, and a nested-interval construction.

**Proposition 5.1 is formalized on this branch under its fixed analytic,
derivative and Wronskian hypotheses. Theorem 1.2 remains in progress.**

The [statement comparison](docs/STEP14_PT.md) checks these hypotheses and
definitions against Proposition 5.1 in the repository manuscript.

[Manuscript](paper/main.pdf) · [Proof roadmap](docs/ROADMAP.md) ·
[Formalized results](docs/FORMALIZATION.md) · [Validation record](VALIDATION.md) ·
[Guia em português](GUIA_PT.md)

## Current status

The [two-height counting theorem](MahlerLean/TwoHeightCounting.lean) combines
small and large target blocks to prove Proposition 5.1 for the original
`dangerousSources` and safety margin. The leading constant is chosen before
the source subinterval and approximation order; the remainder constant and
threshold are uniform in the target-height cutoff. It also supplies the
`HasUniformDangerBound` interface used by fusion.
See the [determinant and counting overview](docs/STEP13_PT.md).
The [Step 12 overview](docs/STEP12_PT.md) records the analytic hypotheses and
scope. These additions have not yet been merged into `main`.

| Part of the argument | Formalization status |
| --- | --- |
| Farey separation and upper counting | Proved for a supplied disjoint interval decomposition. |
| Rational source supply | Proved with the absolute constant $c_F=1/4$. |
| Infinite fusion and Liouville escape | Counting and derivative bounds discharged; Wronskian nontriviality remains explicit. |
| Wronskian localization | Proved under explicit nontriviality hypotheses. |
| Uniform jets and one-dimensional sublevels | Proved. |
| Uniform analytic sublevels | Proved, including a pairwise-disjoint rational-family specialization. |
| Arithmetic determinant lower bound | Proved, without reduced-fraction assumptions. |
| Analytic determinant and rank-to-counting core | Proved on this branch. |
| Full scale/cell assembly of Proposition 5.1 | Proved, including small and large target blocks and uniformity in the cutoff. |
| Theorem 1.2 from the manuscript's hypotheses | Pending. |

[Local analytic escape](MahlerLean/AnalyticDerivativeInterval.lean) now
works in every nonempty open subset of the domain. Counting and derivative
bounds are proved internally. The remaining implication is Wronskian
nontriviality from nonrationality, followed by the final application to
Theorem 1.2. See the [derivative localization notes](docs/STEP15_PT.md).
The uniform sublevel result assumes analyticity; the more general
finite-smoothness statement in the manuscript is not claimed.

## Build the Lean files

Install Lean using the [Lean community installation guide](https://leanprover-community.github.io/get_started.html).
From the root of a checkout, run:

```bash
lake exe cache get
lake build
```

The project pins Lean 4.24.0 and the exact dependency revisions in
`lean-toolchain` and `lake-manifest.json`.
Use these recorded versions when reproducing the proofs.

To run the full verification, including warnings as errors and the
listed-theorem axiom audit:

```bash
bash scripts/check.sh
```

The [GitHub workflow](https://github.com/DiegoMarquesMath/MahlerLean/actions/workflows/lean.yml)
runs these checks automatically. The audit inspects the declarations in
[scripts/Audit.lean](scripts/Audit.lean) and rejects dependencies on
`sorryAx`. Formal correctness applies to the Lean statements with their
explicit hypotheses; it does not certify unformalized claims in the manuscript.

## Exploring the proof

- [MahlerLean.lean](MahlerLean.lean) imports the formalization.
- [Formalized results](docs/FORMALIZATION.md) maps declarations to the mathematical argument.
- [Proof roadmap](docs/ROADMAP.md) describes the dependencies and remaining work.
- [Development notes](docs/) contain detailed explanations of each stage.

## Source and citation

The reference text is the manuscript stored in
[paper/main.pdf](paper/main.pdf), with [LaTeX source](paper/main.tex).
When citing the formalization, include the repository URL and the commit
used, so that readers can identify the exact statements and verification
status.

Maintained by [Diego Marques](https://github.com/DiegoMarquesMath).
