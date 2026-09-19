# Mahler's Question on Liouville Numbers

Lean 4 project for work towards formalizing results in Diego Marques,
*Mahler's problem on Liouville numbers*, manuscript dated 18 September 2026.

**Scope:** the project contains 154 listed theorems. It proves the rational
source supply in Lemma 2.2 with the absolute constant **cF = 1/4**, and
formalizes the infinite fusion construction and its escape conclusion
**conditional on explicit counting, derivative and finite-forbidden-set
inputs**. The theorem `exists_escape_of_uniform_counting` starts from those inputs,
constructs the sequence, and proves the existence of a Liouville point
whose image satisfies an eventual approximation lower bound with exponent
100 and is not Liouville. The common point of the constructed intervals
is unique, and the reduced source denominators tend to infinity.

The project also proves rational separation and the upper counting bound
`4 Q^2 |E| + R` for a finite rational set covered by an explicitly supplied
decomposition into at most R disjoint intervals. This is the component
form of Lemma 2.1, proved without any counting estimate as a hypothesis.

Step 8 constructs the finite Wronskian zero sets from analyticity and explicit
nontriviality hypotheses, and proves their nesting. Step 9 formalizes the
large-target parameter inequalities used in Proposition 5.1. Step 10
formalizes the compactness and linear-algebra core of Lemma 3.5, including
uniform lower bounds for normalized jets and the rational-family specialization.

Proposition 5.1, the determinant lemmas, and the implication from
nonrationality to Wronskian nontriviality remain unproved on `main`.
Step 11 formalizes the one-dimensional sublevel estimate of Lemma 3.4,
including the explicit bound
`2 k (2 k + 1) (eps/lambda)^(1/k)`. Rational source supply is discharged by a theorem.
Theorems 1.1 and 1.2 are **not** fully formalized. No pending result is
installed as an axiom or an unproved placeholder.
Step 12 has begun with the analytic linear-combination bridge: derivatives
of `jetLinearCombo` are identified with the jet coordinates from Step 10,
and analyticity supplies the regularity hypotheses from Step 11. The finite
product-cover and uniform component arguments of Lemma 3.5 remain pending.

For the Portuguese installation guide, open [GUIA_PT.md](GUIA_PT.md).
For the mathematical work plan, open [docs/ROADMAP.md](docs/ROADMAP.md).
For the actual validation record, open [VALIDATION.md](VALIDATION.md).
For the safe-center implication, open [docs/STEP2_PT.md](docs/STEP2_PT.md).
For the conditional fusion conclusion, open [docs/STEP3_PT.md](docs/STEP3_PT.md).
For one local successor step, open [docs/STEP4_PT.md](docs/STEP4_PT.md).
For the infinite construction, open [docs/STEP5_PT.md](docs/STEP5_PT.md).
For Farey separation and upper counting, open [docs/STEP6_PT.md](docs/STEP6_PT.md).
For the proved rational supply and its fusion application, open [docs/STEP7_PT.md](docs/STEP7_PT.md).

For analytic zero sets and Wronskian localization, open [docs/STEP8_PT.md](docs/STEP8_PT.md).
For the large-target parameter inequalities, open [docs/STEP9_PT.md](docs/STEP9_PT.md).
For uniform jet lower bounds, open [docs/STEP10_PT.md](docs/STEP10_PT.md).
For the one-dimensional sublevel estimate, open [docs/STEP11_PT.md](docs/STEP11_PT.md).
For the Step 12 bridge and its exact remaining tasks, open [docs/STEP12_PT.md](docs/STEP12_PT.md).

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
power estimates. Rational supply was subsequently proved in step 7; Proposition 5.1 remains pending.

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

`FusionData f` records the geometric and arithmetic invariants needed for
the conclusion. Step 5 constructs it from the explicit `FusionInputs f`
interface; deriving those inputs from the analytic assumptions of the
paper remains pending. The conclusion gives the inequality with exponent
100; no definition of the irrationality exponent or theorem about its
supremum is installed yet.

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
theorems. Its existence follows from the stated local assumptions and is
used by the infinite recursion. The finite set `Z` is fixed before choosing Q;
step 8 identifies it with the analytic Wronskian zero set, conditional
on Wronskian nontriviality. Step 5 uses `Qmin = 2*q_previous+1` to enforce
source denominator growth during recursion.

The geometric proof uses separated closed intervals and finite cardinality
instead of connected components, with the same exact length as the paper.
No change to the manuscript is needed for this alternative proof.

## Infinite fusion from explicit counting inputs

| Declaration | Manuscript connection |
| --- | --- |
| `exists_initial_tail_cutoff` | Initial H >= 2 with sufficiently small H^(-98) |
| `exists_initial_fusion_stage` | Initial interval avoiding Z_0 and initial cutoff |
| `exists_fusion_transition` | The local step applies to every valid stage |
| `fusionStages_succ` | Exact recursion equation for the sequence |
| `exists_fusion_construction` | Infinite construction satisfying (F1)--(F7) |
| `fusion_intersection_subsingleton` | Source errors force two common points to coincide |
| `exists_unique_fusion_point` | Exactly one point lies in all fusion intervals |
| `fusion_denominators_tendsto` | Reduced source denominators tend to infinity |
| `exists_escape_of_counting` | Counting inputs imply a Liouville escape point in the ambient interior |

`FusionInputs f` fixes an ambient interval, M, Clow, cF, and a sequence of
finite sets Z_n. It requires supply on every compact subinterval and the
uniform counting estimate at exponent n+3 on subintervals avoiding Z_n.
Clow is fixed throughout the recursion. The remainder constant and
threshold can vary with the interval and stage, but are independent of H.

`fusionConstruction` builds `FusionConstruction`, which extends
`FusionData` with strict interval nesting, avoidance of Z_n, source
denominator growth and the tail invariant at every stage. No sequence of
intervals or safe centers is assumed in the counting-to-escape theorem.
The function is noncomputable in Lean because it uses classical choice;
this concerns extracting executable numerical data, not missing proofs.

## Farey separation and upper counting

The upper-counting results are:

| Declaration | Manuscript connection |
| --- | --- |
| `rational_separation` | Distinct reduced fractions differ by at least 1/(qq') |
| `denominator_block_separation` | Strict spacing greater than 1/(4Q^2) |
| `card_le_of_separated_values` | Packing in an interval: cardinality <= length/delta + 1 |
| `rational_interval_card_le` | Upper bound 4Q^2 length + 1 for one interval |
| `sourceFractions_card_le` | The upper bound for the exact project source set |
| `sourceFractions_card_le_one` | A cell of length <= 1/(4Q^2) contains at most one source fraction |
| `rational_ordConnected_card_le_volume` | Upper bound on an interval in terms of Lebesgue volume |
| `rational_union_card_le_volume` | Extended-real bound on a disjoint finite interval union |
| `rational_union_card_le` | Real bound 4Q^2 |E| + R for finite-volume unions with supplied components |

The last theorem takes a finite family of order-connected, pairwise
disjoint real sets, a covering of the rational set by that family, and
the denominator bound. It handles open, closed, half-open, singleton and
empty intervals. It does not produce components from an overlapping
interval cover or prove the analytic sublevel-component bound. The
complementary source-supply estimate of Lemma 2.2 is now proved below.

## Rational supply and its fusion application

`sourceFractions_quarter_supply` proves `HasSourceSupply l u (1/4)` for
arbitrary real endpoints l < u. `exists_source_supply_threshold` gives the
same statement with a strictly positive natural threshold. The source set
and the denominator block [Q,2Q) are exactly those already used by fusion.

The Lean proof uses elementary finite estimates in place of the manuscript's
summatory asymptotics. It first proves the uniform discrepancy
`|N_q(J) - |J| phi(q)| <= #divisors(q)` by Möbius inversion, then proves

```text
sum_{Q <= q < 2Q} phi(q) >= (5/18) Q^2 - (5/2) Q,
sum_{Q <= q < 2Q} #divisors(q) <= 2 Q floor(sqrt(2Q)).
```

The gap 5/18 - 1/4 = 1/36 absorbs the error for each fixed positive
interval length. The original manuscript is unchanged. Its sharper
asymptotic coefficient 9/pi^2 is not claimed as a formalized result.

| Declaration | Role |
| --- | --- |
| `mem_reducedNumerators` | Signed numerator convention, including zero |
| `integer_interval_card_discrepancy` | Integer count differs from length by at most one |
| `multiples_interval_card` | Exact rescaling of a multiple count |
| `multiples_interval_discrepancy` | Uniform error one for multiples |
| `coprime_indicator_moebius` | Coprimality indicator as a common-divisor sum |
| `reducedNumerators_card_moebius` | Exact Möbius formula for N_q(J) |
| `totient_eq_moebius_sum` | Totient divisor identity with real division |
| `reducedNumerators_card_discrepancy` | Error at most the number of divisors |
| `sourceFractions_card_eq_sum_numerators` | Exact denominator fibers, without duplicate fractions |
| `sourceFractions_totient_discrepancy` | Summed error for the project source set |
| `sourceFractions_card_ge_totient_sub_divisors` | Lower bound before arithmetic estimates |
| `reciprocal_squares_except_four_le` | Reciprocal-square sum at most 11/18 |
| `positive_multiples_card` | Positive multiples counted by floor division |
| `noncoprime_pairs_card_le` | Union bound for pairs with a common prime factor |
| `coprime_triangle_card` | Triangular coprime count is the totient sum |
| `coprime_pairs_card_le_twice_totient_sum` | Reflection reduces the square to two triangles |
| `totient_sum_lower` | Summatory lower bound (7/36) N^2 |
| `totient_sum_upper` | Summatory upper bound N(N+1)/2 |
| `totient_sum_range_succ` | Passage between the two sum conventions |
| `totient_block_lower` | Block lower bound (5/18) Q^2 - (5/2) Q |
| `divisors_card_le_twice_sqrt` | Pairing divisors around the square root |
| `block_divisors_card_le` | Block error at most 2 Q floor(sqrt(2Q)) |
| `sourceFractions_card_lower_explicit` | Explicit finite lower estimate for any interval |
| `sourceFractions_quarter_supply` | Lemma 2.2 with cF = 1/4 |
| `exists_source_supply_threshold` | Same lemma with a positive natural threshold |
| `exists_escape_of_uniform_counting` | Fusion and escape with source supply proved |

`UniformCountingInputs` retains the ambient interval, derivative bound,
finite forbidden sets and uniform dangerous-source estimate, but has no
source-supply field. Its `toFusionInputs` inserts the proved estimate at
cF = 1/4. The older general `FusionInputs` interface remains available.
No part of this step proves the dangerous-source estimate of Proposition 5.1.

## Analytic zero sets and Wronskian localization

Step 8 adds 15 theorems in three modules. The analytic Wronskian criterion
is **not** assumed as a library theorem or installed as an axiom.
Nontriviality of each relevant Wronskian is an explicit hypothesis.

| Declaration | Role |
| --- | --- |
| `analytic_zeros_finite_on_compact` | Identity theorem and compactness imply finitely many zeros |
| `exists_analytic_zero_finset` | Exact finite union of zeros from a finite analytic family |
| `exists_pos_abs_lower_bound` | Continuous nonvanishing function has a positive compact lower bound |
| `exists_uniform_pos_abs_lower_bound` | One lower bound for a finite family |
| `exists_interval_analytic_family_separated` | Smaller closed interval with simultaneous separation |
| `wronskian_analytic` | Determinant of analytic derivatives is analytic |
| `rationalFamily_analytic` | Analyticity of x^i f(x)^j in lexicographic order |
| `rationalWronskian_analytic` | Analyticity of W_d |
| `rationalWronskian_zeros_finite` | Compact finiteness, conditional on W_d not identically zero |
| `exists_rationalWronskian_zero_finset` | Exact union for the specified finite degree set |
| `exists_interval_rationalWronskians_separated` | Simultaneous positive separation of those W_d |
| `wronskianDegreeCutoff_monotone` | D(A)=max(2,ceil(10A/97)) is nondecreasing |
| `mem_wronskian_zeroSet` | Exact membership in the manuscript's Z_n |
| `wronskian_zeroSet_mono` | Z_n is contained in Z_m for n <= m |
| `exists_escape_of_wronskian_counting` | Escape with analytic finite zero sets constructed |

`WronskianCountingInputs` requires analyticity on a preconnected domain,
a compact ambient interval in that domain, an upper derivative bound,
nontriviality of W_d for d>=2, and the uniform dangerous-source estimate
on intervals avoiding those Wronskian zeros. Its adapter proves
differentiability and supplies the finite sets `Z_n` to the existing fusion.
The remainder coefficient and threshold retain independence of H.

The simultaneous lower bound can depend on the chosen finite degree set
and interval. No uniform bound over all degrees or all shrinking intervals
is claimed. Uniform sublevel estimates, the determinant counting argument,
and the derivation of Wronskian nontriviality from nonrationality remain open
formalization tasks. The main theorems are still not fully formalized.

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
