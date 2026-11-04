# Contributing to MahlerLean

Thank you for helping improve the mathematical reliability, formal proofs, and
documentation of MahlerLean.

## Scope and proof status

The repository contains an **earlier formalization** in `MahlerLean/` and a
separate **new program** for *Diophantine Rigidity of Analytic Graphs* in
`AnalyticGraphs/`. Do not infer that the old degree-one counting theorem
proves the new arbitrary-degree theorem.

All new research statements must be matched against the **exact revised
manuscript** before being marked verified. Read [AGENTS.md](AGENTS.md),
[the 12-stage plan](docs/ATH_FORMALIZATION.md), and
[the verification policy](docs/ATH_VERIFICATION.md).

## Setting up

Keep the pinned `lean-toolchain` and `lake-manifest.json` unless a separate
review explicitly authorizes a version change.

```bash
lake exe cache get
lake build AnalyticGraphs
bash scripts/check_analytic_graphs.sh
```

The earlier library is checked by `bash scripts/check.sh`; both commands are
included in the GitHub Actions workflow.

## Pull request standards

1. Open a focused draft PR against `main`; do not merge automatically.
2. Link the exact source statement and describe its quantifier order, uniform
   constants, degree restrictions, and endpoint cases.
3. Distinguish code infrastructure, helper lemmas, complete main theorems,
   and exact manuscript-statement verification.
4. Include the full type of each new principal declaration and its
   `#print axioms` result.
5. Never use `sorry`, `admit`, arbitrary axioms or hidden theorem-equivalent
   hypotheses to present a theorem as proved.
6. Run the relevant checks and report failures honestly. A compiling
   scaffold is not certification of an unimplemented result.
7. Record gaps as issues using the proof-obligation template, with an exact
   mathematical statement and minimal reproduction.

## Publication boundary

The revised manuscript may be unpublished. **Do not commit, upload,
quote extensively, or publish `paper/ATH_rev.tex` or `paper/ATH_rev.pdf`
without the author's explicit authorization.** Internal statement-audit notes
can also reveal unpublished material; review them before public publication.

## Citation

Use [CITATION.cff](CITATION.cff) for the software citation. For claims
about a specific formal theorem, cite the exact verified commit and
the corresponding mathematical manuscript.
