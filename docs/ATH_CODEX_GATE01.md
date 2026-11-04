# Codex task — Gate 01: lock the revised proof statements

You are the mathematical formalization agent for *Diophantine Rigidity of Analytic Graphs*.
Read `AGENTS.md` and treat its proof-integrity rules as mandatory.

## Authoritative sources
- `paper/ATH_rev.tex` is the exact revised manuscript, NOT `paper/main.tex`.
- `paper/ATH_rev.pdf` is for cross-checking mathematical typography.
- `docs/ATH_FORMALIZATION.md` and `docs/ATH_PROOF_CONTRACTS.md` are provisional.
- `MahlerLean/` contains previous formalization; reuse only declarations with matching types.

## Goal of this execution

1. Ensure `paper/ATH_rev.tex` and `paper/ATH_rev.pdf` are present. If either is missing, **stop** and report the missing source; do not guess from the old paper.
2. Read the revised manuscript systematically. Extract the exact statements of (FT), Lemmas 3.1–3.2, 4.1–4.2, 5.1, 6.1–6.2, 7.1, and Theorems 1.1, 1.2, 1.4 and 2.1, plus Corollary 1.3.
3. Produce `docs/ATH_STATEMENT_AUDIT.md`: one row per result with exact quantifier order, full assumptions, endpoint conditions, reference labels, mathematical dependencies and any mismatch with `docs/ATH_PROOF_CONTRACTS.md`.
4. Inspect the existing `AnalyticGraphs/PolynomialWitnesses.lean` definitions against the actual mathematical meaning of the manuscript. In particular verify reduced denominator, real B height interval, nonprimitive witnesses, exact zero and distinct rational counting. Correct only genuine mismatches.
5. Search `MahlerLean/` for existing precise lemmas to reuse; document verified declarations and *why* they match. Do not treat the old degree-one two-height estimate as the new arbitrary-degree theorem.
6. Execute `lake build AnalyticGraphs` and `bash scripts/check_analytic_graphs.sh`. If the new scaffold has a compilation error, fix it in `AnalyticGraphs/` (not the old library), rerun the checks and report exactly what passed.
7. Begin the next gate only with elementary, small and fully compilable helper lemmas if the source lock is complete. Do not pretend the main theorem has been proved.

## Hard boundaries
- Do not modify `paper/ATH_rev.tex`, `paper/ATH_rev.pdf` or files under `MahlerLean/`.
- Do not add proof placeholders, custom axioms, weaker target theorems, circular assumptions, or extra hypotheses.
- Do not publish or git-push the manuscript; this is a public repository and the author decides when to publish.
- Do not automatically merge any PR.
- Report every unresolved blocker explicitly, with line numbers or theorem references.

## Required final response

Provide (i) changes made, (ii) mathematical statement comparison results, (iii) build/axiom status, (iv) unresolved obstacles, and (v) the single next concrete lemma to formalize. Do not claim full certification.
