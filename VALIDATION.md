# Validation record

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
