# Diophantine Rigidity of Analytic Graphs — Lean 4 program

**Manuscript:** `paper/ATH_rev.tex` (author's revised version; to be imported).
**Target:** Lean 4.24.0 / pinned mathlib, with a separate `AnalyticGraphs` library.
**Initial state:** prior MahlerLean infrastructure reused; the new research
theorems are **not** yet formalized.

## Twelve gates

Each gate passes only when (a) the Lean statements match the revised paper,
(b) the proofs compile without admitted gaps, (c) the axiom audit is acceptable,
and (d) all preceding gates on which it depends are passed.

| Gate | Mathematical deliverable | Paper location | Key obligation |
| --- | --- | --- | --- |
| **01 · Source lock** | Check exact `ATH_rev.tex` and PDF; pin source hash and theorem map | Whole paper | No statement drift from the revised manuscript |
| **02 · Arithmetic foundations** | Coefficient height, content, primitive factors, degree and reduced rational blocks | §2 | Integral specializations and normalizations |
| **03 · Finite type / real analysis** | (FT) and uniform analytic Taylor/jet controls | §2 | Quantifier order and common derivative bounds |
| **04 · Determinant reconstruction** | Local relations, Lemma 3.1 | §3 | Small columns, integral kernel, `w > M` |
| **05 · Hankel recovery** | Irreducible witness reconstruction, Lemma 3.2 | §3 | Quotient field, nondegenerate pairing, gcd removal |
| **06 · Projective content** | Lemma 4.1 | §4 | Two p-adic charts, congruence balls, uniform height factor |
| **07 · Integral resultants** | Lemma 4.2 | §4 | Sylvester determinant, degree-zero case |
| **08 · Multiscale propagation** | Lemma 5.1 | §5 | Same F; density retained; no accumulation of errors |
| **09 · Two-height counting** | Lemas 6.1–6.2; Theorems 1.1 and 2.1 | §6 | Irreducible factors, dyadic heights, uniform power saving |
| **10 · Metric tail and Cantor** | Lemma 7.1; Theorem 1.2 | §7 | All m simultaneously, every branch, transcendental images, mu=2 |
| **11 · Arithmetic descent** | Theorem 1.4; Proposition 8.1 | §8 | Rational line of minimal equation and bounded integral height |
| **12 · Integration and certification** | Full corollary dependency route, independent statement audit, CI and report | §§7–9 | No hidden assumptions; reproducible commit hash |

Section 9 (pointwise threshold) is a separate useful verification target.
It is independent of the main counting-to-Cantor chain and should not delay
the core theorem unless it exposes a foundational fault.

## Critical dependency DAG

```text
heights + rational blocks + analytic finite type
           |
           v
3.1 determinant relation --> 3.2 Hankel recovery
                                      |
4.1 content --------------------------+----> 5.1 propagation
4.2 resultant ------------------------+            |
                                                   +--> 6.1 finite-type contradiction
                                                   |        |
                                                   |        v
6.2 sublevel / irreducible reduction ---------------+--> 1.1 / 2.1 counting
                                                   |               |
                                                   |               v
                                                   |            7.1 metric tail
                                                   |               |
                                                   |               v
                                                   |            1.2 Cantor / S-numbers
                                                   |
                                                   +--> 1.4 arithmetic descent

previous MahlerLean entire-rigidity --> statement of Corollary 1.3 (legacy route)
new Theorem 1.2 ---------------------> Corollary 1.3 (target new route)
```

## Working protocol

Open a PR per high-risk lemma or small tightly coupled module.
Keep the exact paper statement in the relevant file docstring.
Write tests for finite identities but never mistake tests for general proofs.
Any claim of completion must include the proof commit SHA, the `lake build`
result, the axiom output and a human-reviewed statement comparison.

## Current checkpoint

- [x] Old formalization identified and isolated.
- [x] New library structure and basic definitions introduced (pending CI).
- [x] Entire-function corollary connected to the legacy formal proof.
- [ ] Revised manuscript copied and its exact statements compared.
- [ ] Gates 03–12 completed for the new counting method.

This checklist is conservative by design.
