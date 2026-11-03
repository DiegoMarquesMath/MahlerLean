# Agent instructions — mathematical formalization

## Mission

Formalize *Diophantine Rigidity of Analytic Graphs* against the **exact revised source**
`paper/ATH_rev.tex`, using Lean 4.24.0 and the lockfile in this repository.
Build proofs of precisely stated theorems, not similarly named weaker variants.
The original `MahlerLean/` source is historical, stable infrastructure.

## Non-negotiable proof standards

1. Never introduce `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide` or an unchecked external proof oracle to discharge research claims.
2. Never assume the target theorem (or a mathematical equivalent) through a typeclass, structure field, helper lemma, parameter or existential premise.
3. Do not silently weaken quantifiers, drop exact-zero cases, add genericity hypotheses, replace a uniform estimate with a nonuniform one or change the paper's exponent.
4. Every new result must have an explicit statement-level comparison with the cited lemma or theorem in `paper/ATH_rev.tex`, including constants, scopes and dependency order.
5. Separate: (i) definition implemented, (ii) helper proved, (iii) main theorem proved, (iv) axiom check passed, (v) manuscript statement verified. Never equate these statuses.
6. Do not edit `paper/main.tex`, the old `MahlerLean/` tree, the pinned toolchain or existing validation history unless explicitly required for an independently reviewed compatibility fix.
7. Do not falsely say "formalized" when only a Lean skeleton compiled. A failed proof attempt is a useful outcome: record the exact missing mathematical lemma.
8. Use proof-focused commits and a draft PR. Do not merge the branch automatically.

## Workflow per stage

- Read only the relevant LaTeX statement, proof and prerequisite Lean modules.
- Write a short statement contract; list every quantified parameter and boundary case.
- Search mathlib and the legacy code for *matching* lemmas; verify their types with `#check`.
- Implement one or a few small mathematical lemmas at a time.
- Run `lake build AnalyticGraphs` and `bash scripts/check_analytic_graphs.sh`.
- Extend `scripts/AuditAnalyticGraphs.lean` with every completed principal declaration.
- Inspect `#print axioms`, check that no new project axioms or `sorryAx` occur.
- Update the verification matrix, record any discrepancy between paper and Lean, and make one small commit.
- If blocked, stop at the obstruction and write a precise issue. Do not manufacture a proof or dilute the statement.

## Priorities

Follow `docs/ATH_FORMALIZATION.md`. Treat projective content (Lemma 4.1),
uniform propagation (Lemma 5.1), and the measure-theoretic Cantor step
as the highest-risk new mathematical components.
