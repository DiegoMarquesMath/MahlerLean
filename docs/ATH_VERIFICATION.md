# Verification standard

## What a green check means

The GitHub Actions job checks the old library, builds the
`AnalyticGraphs` library, checks the source files and prints axioms
for every declaration listed in `scripts/AuditAnalyticGraphs.lean`.
At the initial checkpoint this list contains only **basic definitions,
the membership theorem and inherited results**. Green CI does *not*
mean that the new manuscript's main theorem is formalized.

## The full certification gate

A main theorem may be marked **verified** only when all five items are true:

1. The exact Lean proposition matches the revised paper, including
   all hypotheses, all quantifiers and every edge case.
2. Its proof and all transitive dependencies compile in the pinned Lean
   toolchain, using mathlib as recorded in the lockfile.
3. The project uses no unproved placeholders, extra axioms,
   oracle escapes or hidden equivalent hypotheses.
4. The theorem is in the central axiom-audit file, and its
   `#print axioms` output was examined (usual logical foundations
   `propext`, `Classical.choice`, `Quot.sound` are expected).
5. A separate reviewer compares the mathematical meaning of the
   final formal statement with `paper/ATH_rev.tex`.

For additional defense in depth, run the Lean kernel/olean checker on
the finished proof modules when available with the pinned toolchain.
A source grep and `#print axioms` alone are not a proof of statement fidelity.

## Current verified scope

The new workstream initially imports Farey bounds and the exact
entire-function rigidity statement from the legacy project.
The new arbitrary-degree two-height theorem, propagation,
Mahler-exponent Cantor theorem and arithmetic descent remain
**open mathematical formalization tasks**.

## Reproduction

```bash
lake exe cache get
lake build AnalyticGraphs
bash scripts/check_analytic_graphs.sh
bash scripts/check.sh
```

Before publishing a formalization milestone, capture the exact
source commit hash, Lean version, mathlib manifest, successful CI run,
axiom output, and statement-matching review in this document.
