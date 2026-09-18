# MahlerLean

Initial Lean 4 project for work towards formalizing results in Diego Marques,
*Mahler's problem on Liouville numbers*, manuscript dated 18 September 2026.

**Scope:** this starter project contains nine elementary supporting lemmas.
It does **not** formalize Proposition 5.1, the complete fusion construction,
or Theorems 1.1 and 1.2. No statement of those main results is installed as
an axiom or an unproved placeholder.

For the Portuguese installation guide, open [GUIA_PT.md](GUIA_PT.md).
For the mathematical work plan, open [docs/ROADMAP.md](docs/ROADMAP.md).
For the actual validation record, open [VALIDATION.md](VALIDATION.md).

## Reproduce

Install the official Lean 4 extension in VS Code and finish its setup guide.
Open this whole folder in VS Code. In a terminal inside this folder, run:

```bash
lake update
lake exe cache get
lake build
bash scripts/check.sh
```

The initial dependency configuration deliberately uses matching Lean and
mathlib `v4.24.0` releases. This is a fixed baseline, not a claim that this
is the latest release. Elan selects the Lean version recorded in
`lean-toolchain`. Keep `lake-manifest.json` in Git to retain exact revisions.
After a manifest exists, ordinary daily checks need only `lake build` and
`bash scripts/check.sh`; do not routinely update dependencies.

## Implemented statements

| Declaration | Manuscript connection |
| --- | --- |
| `dyadic_exponent_identity` | 33/20 + 1/20 = 17/10, after (5.44) |
| `remainder_exponent_lt_two` | 17/10 < 2 |
| `farey_exponent_gt_two` | 97/35 > 2, (5.42) |
| `perturbation_gap` | Gap (5.28), conditional on the preceding inequalities |
| `fusion_exponent_identity` | Exponent identity in (6.26) |
| `fusion_exponent_negative` | Negativity for positive A |
| `exists_safe_center` | Finite-set counting principle |
| `counting_budget` | Two quarter-budget bounds leave a strict margin |
| `safety_transfer` | Abstract triangle-inequality step (6.19)--(6.20) |

These are small components of the proof, not complete numbered results of
the manuscript. In particular, `exists_safe_center` does not prove Lemma 6.1:
the rational supply and the counting estimate must still be established.

## Verification policy

- Add each new module to the imports in `MahlerLean.lean`.
- Add each new claimed result to `scripts/Audit.lean`.
- Inspect both the theorem statement and `#print axioms` output.
- The usual foundational axioms `propext`, `Classical.choice`, and
  `Quot.sound` are expected in classical mathematics. An unexpected axiom
  needs investigation; `sorryAx` is an unproved placeholder.
- A build success alone does not certify every claim in the manuscript.
- The GitHub workflow builds the project and runs the listed-theorem audit.

No open-source license has been selected for this initial package.
Choose one before inviting unrestricted public reuse or contributions.
