# Validation record — initial commit

Validated on 18 September 2026 in a Linux x86_64 environment.

- Lean: 4.24.0, commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`.
- mathlib: tag v4.24.0, commit
  `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`.
- `lake build`: passed, 857 jobs.
- Both project source modules were checked with `warningAsError=true`:
  passed, without warnings.
- `scripts/Audit.lean`: checked all nine listed theorems.
- No listed theorem depends on `sorryAx` or an additional project axiom.
- Eight results use only `propext`, `Classical.choice`, `Quot.sound`.
- `exists_safe_center` uses only `propext`, `Quot.sound`.
- `bash scripts/check.sh`: exit code 0.
- Every named theorem in the two initial source modules has an audit entry.
- The TOML configuration, workflow YAML, and shell syntax were also checked.

The relevant precompiled mathlib modules were downloaded using:

```bash
lake exe cache get Mathlib.Data.Real.Basic Mathlib.Data.Finset.Card Mathlib.Tactic.Linarith Mathlib.Tactic.NormNum Mathlib.Tactic.Ring
```

The generic `lake exe cache get` in the beginner guide downloads a larger
cache and is also the standard setup route for an existing mathlib project.

Not performed: installation on the user's Mac, creation of a GitHub remote,
or execution of the supplied workflow on GitHub Actions. The GitHub connection
was confirmed, but repository-operation tools were not exposed in this session.
The workflow has been prepared, not remotely executed.

The main theorem and Proposition 5.1 are not formalized in this package.


# Step 2 — counting to safe-center selection

Validated on 18 September 2026 in Linux x86_64, with the same Lean 4.24.0
and mathlib v4.24.0 revisions recorded above. No dependency update was made.

Reference manuscript: the uploaded `main.tex`, SHA-256
`4ac94b1f36e6a48103b25344e8e736657cef2cb5944c600c5afe098119f8b995`.

- `lake build`: passed, 1904 jobs.
- All four source modules passed with `warningAsError=true`.
- `bash scripts/check.sh`: exit code 0.
- The audit includes all 16 named project theorems, including all seven
  new declarations.
- The seven new theorems depend only on `propext`, `Classical.choice`,
  and `Quot.sound`.
- No listed theorem depends on `sorryAx` or an additional project axiom.
- The complete project audit still gives only the foundational axioms
  described in the initial validation.

New modules: `RationalBlocks.lean` and `CountingToSafeCenter.lean`.
The exact statements and pending hypotheses are explained in
`docs/STEP2_PT.md`. In particular, `HasSourceSupply` and
`HasUniformDangerBound` are definitions of explicit assumptions, not
proofs of Lemma 2.2 and Proposition 5.1.

The user's screenshot confirms that the initial package built and its
first local commit was created on the Mac. This step-2 update was tested
here on Linux; the supplied terminal commands repeat its checks on the
Mac before committing. No GitHub publication or Actions run was performed.
