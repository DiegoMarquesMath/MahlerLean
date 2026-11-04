## Mathematical objective

State the precise theorem or supporting lemma. Provide the manuscript
reference (section, label, and revision/hash) or explain that this is
infrastructure only.

## Statement comparison

- [ ] The Lean proposition agrees with the mathematical source, including all quantifiers
- [ ] Constants are uniform over exactly the ranges asserted
- [ ] Exact zeros, degree drops, nonprimitive/repeated factors and endpoints are handled where applicable
- [ ] No extra hypothesis has been added to make the statement easy to prove

## Verification evidence

- [ ] `lake build AnalyticGraphs` succeeded (attach output/CI link)
- [ ] `bash scripts/check_analytic_graphs.sh` succeeded
- [ ] Principal declarations have been added to the axiom audit
- [ ] `#print axioms` was inspected; no `sorryAx` or unapproved new axiom
- [ ] A reviewer compared the formalized theorem with the manuscript

**Exact declaration(s):**  
**Proof commit:**  
**Lean/mathlib versions:**  
**Remaining gaps or blockers:**

## Scope and publication

- [ ] Legacy `MahlerLean/` was left unchanged, or modifications are justified
- [ ] Manuscript and unpublished notes are not included without author approval
- [ ] Status claims in the README and docs are no stronger than the evidence
