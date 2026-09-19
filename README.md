# Mahler's Question on Liouville Numbers

[![Lean verification](https://github.com/DiegoMarquesMath/MahlerLean/actions/workflows/lean.yml/badge.svg)](https://github.com/DiegoMarquesMath/MahlerLean/actions/workflows/lean.yml)

This repository contains a Lean 4 formalization accompanying Diego Marques's
work on Mahler's question about Liouville numbers. The project is focused on
the two-height counting argument and the nested-interval construction behind
the local quantitative theorem.

## Mathematical goal

Let $U \subseteq \mathbb R$ be an open interval and let
$f : U \to \mathbb R$ be real-analytic and nonrational. The main target is
to formalize the statement that every nonempty open subinterval of $U$
contains a Liouville number $\xi$ such that

$$
\mu(f(\xi)) \le 100.
$$

The central counting input is a uniform two-height estimate of the form

$$
\#\mathcal D(J;Q,A,H)
\le C_{\mathrm{low}}Q^2H^{-98}+C(J,A)Q^{17/10},
$$

with the remainder constant and threshold independent of $H$.

## Project status

The formalization is in active development.

Verified components currently include:

- rational separation and the upper bound $4Q^2|E|+R$;
- rational source supply with the absolute constant $c_{\mathrm F}=1/4$;
- analytic zero localization and finite Wronskian forbidden sets, conditional
  on Wronskian nontriviality;
- the parameter inequalities used in the large-target range;
- uniform lower bounds for normalized jets;
- the one-dimensional sublevel estimate
  $2k(2k+1)(\varepsilon/\lambda)^{1/k}$;
- the complete abstract fusion construction and its escape conclusion,
  conditional on the uniform dangerous-source estimate.

Still in progress:

- uniform sublevel length and component bounds;
- Wronskian nontriviality derived from nonrationality;
- the anisotropic determinant estimates;
- Proposition 5.1, including both target-height ranges;
- the final unconditional derivation of Theorem 1.2.

No pending mathematical result is installed as an axiom or unproved
placeholder. A successful build should not be interpreted as a claim that
the main theorem is already fully formalized.

## Documentation

- [Manuscript source](paper/main.tex) and [current PDF](paper/main.pdf)
- [Mathematical roadmap](docs/ROADMAP.md)
- [Detailed formalization status](docs/FORMALIZATION_STATUS.md)
- [Validation record](VALIDATION.md)
- [Portuguese installation guide](GUIA_PT.md)
- Step notes:
  [2](docs/STEP2_PT.md),
  [3](docs/STEP3_PT.md),
  [4](docs/STEP4_PT.md),
  [5](docs/STEP5_PT.md),
  [6](docs/STEP6_PT.md),
  [7](docs/STEP7_PT.md),
  [8](docs/STEP8_PT.md),
  [9](docs/STEP9_PT.md),
  [10](docs/STEP10_PT.md),
  [11](docs/STEP11_PT.md)

## Build the Lean project

Install Lean using the
[official installation instructions](https://lean-lang.org/install/), then run:

```bash
git clone https://github.com/DiegoMarquesMath/MahlerLean.git
cd MahlerLean
lake exe cache get
lake build
bash scripts/check.sh
```

The project pins Lean and mathlib through `lean-toolchain` and
`lake-manifest.json`. Ordinary builds should not run `lake update`, since
that may change the verified dependency snapshot.

## Repository layout

| Path | Purpose |
| --- | --- |
| `MahlerLean/` | Lean source modules |
| `MahlerLean.lean` | Root import file |
| `scripts/Audit.lean` | Axiom audit for listed project theorems |
| `scripts/check.sh` | Reproducible build and audit checks |
| `docs/` | Roadmap, detailed status, and step-by-step notes |
| `paper/` | Manuscript source and PDF |
| `.github/workflows/lean.yml` | Continuous verification on GitHub Actions |

## Verification policy

Every claimed project theorem is added to `scripts/Audit.lean`. The automated
workflow builds the project and checks the printed axiom dependencies. The
usual foundational axioms used by classical mathlib developments—`propext`,
`Classical.choice`, and `Quot.sound`—are expected; `sorryAx` or a
project-specific mathematical axiom is not.

For the exact scope of each verified milestone and the hypotheses still
present in the formal statements, see the
[detailed status](docs/FORMALIZATION_STATUS.md) and
[validation record](VALIDATION.md).
