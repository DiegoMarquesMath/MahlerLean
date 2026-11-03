# MahlerLean

**Machine-checked arithmetic rigidity** · Lean 4 + mathlib

[![Lean CI](https://github.com/DiegoMarquesMath/MahlerLean/actions/workflows/lean.yml/badge.svg?branch=main)](https://github.com/DiegoMarquesMath/MahlerLean/actions/workflows/lean.yml)

This repository develops formal proofs around analytic rigidity and Mahler's problem on Liouville numbers. It contains a completed **earlier formalization** and a carefully separated **new formalization program** for *Diophantine Rigidity of Analytic Graphs*.

> **Verification boundary.** A theorem is described as formalized here only when its actual Lean statement has been matched against the paper, its proof has been checked by Lean, and its axioms have been inspected. A successful build of a scaffold is not proof of a research theorem.

## Research tracks

| Track | Mathematical content | Status |
| :--- | :--- | :--- |
| **Mahler's Problem I · Analytic Rigidity** | Rational approximation, Liouville-preserving analytic functions, Cantor refinement and the entire-function corollary | **Previously formalized**; see the [validation record](VALIDATION.md) and [legacy theorem map](docs/FORMALIZATION.md) |
| **Diophantine Rigidity of Analytic Graphs** | Polynomial small values of arbitrary bounded degree; independent heights; finite algebraic type; propagation; S-number images; arithmetic descent | **Formalization in progress**; [12-stage plan](docs/ATH_FORMALIZATION.md) |

The new manuscript studies the count
```math
N_{f,m}(Q,B,w) \ll Q^{2-\eta}
\qquad (w>2m-1,\quad Q^{u_0}\le B\le Q^U),
```
and its Diophantine consequences:
```math
\xi\in\mathscr L,\qquad
f(\xi)\ \text{transcendental},\qquad
w_m(f(\xi))\le 2m-1\quad (m\ge1).
```

These are **target statements**, not yet fully proved in the new Lean library. The previous project addresses a different, degree-one approximation problem and does not by itself certify these stronger claims.

## Code map

```text
MahlerLean/                 Existing formalization (preserved)
AnalyticGraphs/             New manuscript: definitions, bridges and upcoming proofs
MahlerLean.lean             Legacy library entry point
AnalyticGraphs.lean         New library entry point
paper/main.tex              Historical manuscript; kept for reproducibility
paper/ATH_rev.tex           New manuscript: copy from local working folder
paper/ATH_rev.pdf           New manuscript: copy from local working folder
docs/ATH_FORMALIZATION.md   Stages and completion gates
docs/ATH_PROOF_CONTRACTS.md Paper-to-Lean statement specifications
docs/ATH_REUSE_MAP.md       Verified reuse vs new obligations
docs/ATH_VERIFICATION.md    Proof integrity and independent audit policy
scripts/check.sh            Existing project checks
scripts/check_analytic_graphs.sh   New library checks
```

The files `paper/ATH_rev.tex` and `paper/ATH_rev.pdf` are **not yet committed**; they must be copied from the author's desktop before a statement-level comparison can be signed off.

## Reproduce

This repository pins Lean **4.24.0** and the matching mathlib snapshot through `lean-toolchain` and `lake-manifest.json`. Preserve that pin while reusing the legacy proofs.

```bash
git clone https://github.com/DiegoMarquesMath/MahlerLean.git
cd MahlerLean
lake exe cache get
bash scripts/check.sh
bash scripts/check_analytic_graphs.sh
```

To work on the new development branch:

```bash
git fetch origin
git switch feature/analytic-graphs-formalization
lake exe cache get
lake build AnalyticGraphs
```

The new checker currently audits **only the declarations actually implemented**; later milestones must extend its audited list. See [verification policy](docs/ATH_VERIFICATION.md).

## Mathematical method

The intended proof architecture runs from local determinant relations to irreducible polynomial reconstruction, projective specialization content, integral resultants and multiscale propagation. Finite algebraic type then yields the two-height count. A separate metric argument produces Cantor sets with simultaneous Mahler-exponent bounds; the algebraic-branch argument uses the same propagation to obtain arithmetic descent.

The central proof obligations, including exact quantifier order and endpoint cases, are specified in [proof contracts](docs/ATH_PROOF_CONTRACTS.md). The previous formalization offers reusable tools, but not a substitute for the new proofs.

## Integrity

All code changes are reviewed on branches with GitHub Actions; the source files of the earlier project are not modified by this new workstream. New mathematical declarations must not rely on unproved placeholders, custom axioms, hidden hypotheses, or a restatement of their desired conclusion as an assumption. The [agent rules](AGENTS.md) apply equally to human and automated contributions.

## Attribution

**Diego Marques** · Department of Mathematics, Universidade de Brasília.

This repository is research software accompanying mathematical manuscripts. The mathematical statements in the papers, not the status badges, define what must be certified.
