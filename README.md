# MahlerLean

Initial Lean 4 project for work towards formalizing results in Diego Marques,
*Mahler's problem on Liouville numbers*, manuscript dated 18 September 2026.

**Scope:** the project contains 37 listed theorems. They cover supporting
lemmas, rational source sets, conditional safe-center selection, the
Liouville-definition bridge, the conditional conclusion of fusion, and
one local successor step. The theorem `successor_from_counting` now
chooses a scale, safe rational center and next closed interval from
explicit counting, derivative and tail hypotheses and a fixed finite
forbidden set. It preserves the quantitative condition for the next
stage. The theorem `exists_escape_of_fusion_data` derives a Liouville
escape point from a full infinite sequence of intervals and invariants;
constructing that sequence is still pending.

The source supply (Lemma 2.2) and Proposition 5.1 remain explicit hypotheses
of the safe-center selection theorem. The project does **not** prove those two estimates,
the complete fusion construction, or Theorems 1.1 and 1.2. None of these
pending results is installed as an axiom or an unproved placeholder.

For the Portuguese installation guide, open [GUIA_PT.md](GUIA_PT.md).
For the mathematical work plan, open [docs/ROADMAP.md](docs/ROADMAP.md).
For the actual validation record, open [VALIDATION.md](VALIDATION.md).
For the safe-center implication, open [docs/STEP2_PT.md](docs/STEP2_PT.md).
For the conditional fusion conclusion, open [docs/STEP3_PT.md](docs/STEP3_PT.md).
For one local successor step, open [docs/STEP4_PT.md](docs/STEP4_PT.md).

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
Step 2 adds:

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
The conditional theorem connects it to the actual rational sets and
power estimates. The rational supply and Proposition 5.1 still need proofs.

## Fusion conclusion and Liouville conventions

| Declaration | Manuscript connection |
| --- | --- |
| `liouville_iff_paperLiouville` | Library definition equals infinitely many pairs at every positive exponent |
| `liouville_of_source_approximations` | Nonzero source approximation with orders n+3 implies Liouville |
| `not_liouville_of_eventual_target_avoidance` | A fixed eventual approximation lower bound excludes Liouville |
| `exists_target_block` | Consecutive increasing integer blocks cover all denominators above T_0 |
| `target_avoidance_from_blocks` | Blockwise exclusion implies eventual target avoidance |
| `exists_escape_of_fusion_data` | Nested intervals with explicit source/target invariants yield an escape point |
| `safeCenter_avoidance_of_deriv_bound` | Mean-value theorem supplies the movement bound near a safe center |

`FusionData f` is an explicit hypothesis package. No theorem currently
constructs it from the analytic assumptions of the paper. The new
conclusion gives the inequality with exponent 100; no definition of the
irrationality exponent or theorem about its supremum is installed yet.

## One successor step of fusion

| Declaration | Manuscript connection |
| --- | --- |
| `exists_interval_avoiding_finset` | Quantitative interval selection after removing finitely many points |
| `exists_interval_avoiding_zeros_and_center` | Length R/(#Z+2), avoiding Z and the current center |
| `exists_next_interval_in_parent` | The next closed interval lies in the parent's interior |
| `middle_third_length` | Exact length of the next middle third |
| `targetCutoff_pow97` | X^97 = Q^A for X = Q^(A/97) |
| `half_le_nat_floor` | floor(X) >= X/2 for X >= 2 |
| `nextCutoff_le_targetCutoff` | The integer target block stays below the real cutoff |
| `nextCutoff_gt` | Condition (Q3) gives a strictly larger cutoff |
| `fusionRadius_le_source_accuracy` | (2Q)^(-A) <= q^(-A) when q <= 2Q |
| `nextCutoff_tail_le` | Effect of taking the integer part on the exponent -98 |
| `tail_smallness_next` | Condition (Q4) implies the next tail invariant (F7) |
| `exists_large_fusion_scale` | Simultaneous choice of Q above any prescribed minimum |
| `successor_from_safe_center` | Interval, source/target approximation and tail from a safe center |
| `successor_from_counting` | One local successor step from the two counting hypotheses |

`SuccessorInterval` records the data and proofs produced by the last two
theorems. Unlike `FusionData`, its existence is now proved from the stated
local assumptions. The arbitrary finite set `Z` is fixed before choosing Q;
the analytic argument identifying and controlling the Wronskian zeros
has not been formalized. Choosing `Qmin > 2*q_previous` would enforce
the source denominator growth required in a future recursive construction.

The geometric proof uses separated closed intervals and finite cardinality
instead of connected components, with the same exact length as the paper.
No change to the manuscript is needed for this alternative proof.

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
