# Formalization status: Diophantine Rigidity of Analytic Graphs

This is a **research proof dashboard**, not a numerical progress estimate.
A completed CI run proves that the declarations in the repository compile
and satisfy the configured checks; it does **not** establish unimplemented
theorems from the revised manuscript.

## Code and validation checkpoints

- Existing source track: `MahlerLean/`, with its historical
  [validation record](../VALIDATION.md).
- New source track: `AnalyticGraphs/`.
- Development PR: [#4](https://github.com/DiegoMarquesMath/MahlerLean/pull/4)
  (draft; not merged).
- Baseline PR CI: [successful workflow run](https://github.com/DiegoMarquesMath/MahlerLean/actions/runs/41738100763)
  at commit `1f277b46a6edec14c823b6e240e5e810be4de846`.
  This covers the **published scaffold**, not the author's subsequent
  unpushed Mac changes.
- Revised TeX/PDF: author's local working files; their inclusion in this
  public branch is **not authorized by this dashboard**.

## Twelve-stage matrix

| Gate | Deliverable | Status |
| --- | --- | --- |
| 01 | Revised statement correspondence and source lock | **Local audit prepared; full local verification pending** |
| 02 | Polynomial height, contents, primitive factors and denominator conventions | **Definitions introduced; foundation proofs incomplete** |
| 03 | Uniform finite algebraic type | Not yet formalized |
| 04 | Local determinant reconstruction (3.1) | Not yet formalized |
| 05 | Irreducible Hankel reconstruction (3.2) | Not yet formalized |
| 06 | Projective content estimate (4.1) | Not yet formalized |
| 07 | Integral resultant estimate (4.2) | Not yet formalized |
| 08 | Multiscale propagation (5.1) | Not yet formalized |
| 09 | Uniform two-height counting (1.1, 2.1) | Not yet formalized |
| 10 | Cantor set of Liouville arguments and S-number images (1.2) | Not yet formalized |
| 11 | Arithmetic descent (1.4) | Not yet formalized |
| 12 | Final statement, proof and axiom certification | Not yet formalized |

**Do not promote a row to “verified” solely because a source file exists,
a build is green, or a weaker legacy theorem resembles the new statement.**

The priority chain is [proof contracts](ATH_PROOF_CONTRACTS.md) and
[12-stage plan](ATH_FORMALIZATION.md), subject to the exact revised source.
The critical independent audits are the projective content lemma,
uniform propagation, and the measure-theoretic Cantor induction.

## Completion evidence required per gate

A reviewable checkpoint must identify the precise Lean declaration,
source theorem, exact proof commit, complete build check, axiom audit,
and independent statement comparison. Partial results should be
described as such.
