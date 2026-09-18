# MahlerLean

Initial Lean 4 project for work towards formalizing results in Diego Marques,
*Mahler's problem on Liouville numbers*, manuscript dated 18 September 2026.

**Scope:** the project contains the nine initial supporting lemmas and seven
additional theorems for exact rational source sets and the deduction of a
safe center from explicit counting hypotheses. The new theorem
`safe_center_of_counting_estimates` proves the counting-to-selection
implication of Lemma 6.1, including a threshold uniform in H.

The source supply (Lemma 2.2) and Proposition 5.1 remain explicit hypotheses
of this implication. The project does **not** prove those two estimates,
the complete fusion construction, or Theorems 1.1 and 1.2. None of these
pending results is installed as an axiom or an unproved placeholder.

For the Portuguese installation guide, open [GUIA_PT.md](GUIA_PT.md).
For the mathematical work plan, open [docs/ROADMAP.md](docs/ROADMAP.md).
For the actual validation record, open [VALIDATION.md](VALIDATION.md).
For the new statement and its precise scope, open [docs/STEP2_PT.md](docs/STEP2_PT.md).

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

The nine initial results above are small components of the proof.
The next step adds:

| Declaration | Manuscript connection |
| --- | --- |
| `mem_sourceFractions` | Exact source set, with reduced denominator in [Q,2Q) |
| `isSafeCenter_iff_no_witness` | Negation of the target-witness condition |
| `isSafeCenter_iff_not_mem_dangerousSources` | Safety is exclusion from the dangerous source set |
| `eventually_subquadratic_quarter` | C Q^p <= c Q^2 / 4 eventually, for p < 2 |
| `exists_safeCenter_of_quarter_bounds` | Safe rational after the two quarter-budget inequalities |
| `safe_center_of_counting_estimates` | Lemma 6.1 conditional on the two counting inputs, uniform in H |
| `safeCenter_avoidance_of_movement` | Target avoidance after a controlled change in function value |

In particular, `exists_safe_center` alone is only a finite-set principle.
The new conditional theorem connects it to the actual rational sets and
power estimates. The rational supply and Proposition 5.1 still need proofs.

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
