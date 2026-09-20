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


# Step 3 — conclusion of fusion from explicit invariants

Validated on 18 September 2026 in Linux x86_64 with the same pinned
Lean 4.24.0 and mathlib v4.24.0 revisions. No dependency update was made.

- `lake build`: passed, 2172 jobs.
- All six source modules passed with `warningAsError=true`.
- `bash scripts/check.sh`: exit code 0.
- The audit includes all 23 explicitly declared project theorems.
- Every new theorem depends only on `propext`, `Classical.choice`,
  and `Quot.sound`; no listed theorem depends on `sorryAx` or an
  additional project axiom.

New modules: `LiouvilleBridge.lean` and `FusionConclusion.lean`.
The first proves the definition equivalence and pointwise consequences.
The second proves block coverage, the conditional fusion conclusion,
and the mean-value step used near a safe center.

`FusionData f` is explicit input data with hypotheses. Its existence
under the analytic assumptions of the manuscript is not proved.
No theorem about a separately defined irrationality-exponent supremum
is claimed; the quantitative conclusion is the explicit approximation
lower bound from Theorem 1.2.

The user's screenshot confirms that step 2 passed on the Mac and was
committed locally as `66492fb`, with a clean working tree. The present
step-3 update was checked here on Linux; the supplied commands repeat
the checks on the Mac before its next commit. No GitHub publication or
Actions run was performed.


# Step 4 — one successor step from counting hypotheses

Validated on 18 September 2026 in Linux x86_64 with the same pinned
Lean 4.24.0 and mathlib v4.24.0 revisions. No dependency update was made.
The reference manuscript and its SHA-256 remain as recorded in step 2.

- `lake build`: passed, 2175 jobs.
- All nine project source modules passed with `warningAsError=true`.
- `bash scripts/check.sh`: exit code 0.
- The audit includes all 37 explicitly declared project theorems,
  including the 14 new results.
- Every new theorem depends only on `propext`, `Classical.choice`,
  and `Quot.sound`.
- No listed theorem depends on `sorryAx` or an additional project axiom.

New modules: `FiniteAvoidance.lean`, `FusionScale.lean`, `FusionStep.lean`.
They prove quantitative finite-set avoidance, floor-cutoff and tail
estimates, simultaneous scale selection, and one successor step under
explicit local counting, derivative and tail assumptions. The analytic
interpretation of the finite forbidden set, initialization and infinite
recursion, source supply, and Proposition 5.1 remain pending.

The user's screenshots confirm that step 3 passed on the Mac and was
committed locally as `6eb5acf`. Three untracked copies were subsequently
moved to a separate backup folder; the final screenshot shows a clean
working tree. This step-4 update was checked here on Linux; the supplied
commands repeat the checks on the Mac before committing. No GitHub
publication or Actions run was performed.


# Step 5 — infinite fusion and escape from counting inputs

Validated on 18 September 2026 in Linux x86_64 with the same pinned
Lean 4.24.0 and mathlib v4.24.0 revisions. No dependency update was made.
The reference manuscript and its SHA-256 remain as recorded in step 2.

- `lake build`: passed, 2177 jobs.
- All eleven source modules passed with `warningAsError=true`.
- `bash scripts/check.sh`: exit code 0.
- The audit includes all 46 explicitly declared project theorems,
  including the nine new results.
- Every new theorem depends only on `propext`, `Classical.choice`,
  and `Quot.sound`.
- No listed theorem depends on `sorryAx` or an additional project axiom.

New modules: `FusionRecursion.lean`, `FusionEscape.lean`.
The first initializes the interval and cutoff and builds an infinite
sequence satisfying the seven fusion invariants. The second proves
uniqueness of the common point, divergence of the reduced source
denominators, and the escape conclusion from `FusionInputs`.

The existence of `FusionData` is now proved from the explicit supply,
counting, derivative and finite-forbidden-set interface. That interface
is not an axiom and does not assert the desired conclusion. Its analytic
derivation, including Lemma 2.2, Proposition 5.1 and the Wronskian-zero
arguments, remains pending. Theorems 1.1 and 1.2 are not fully formalized.

The user's screenshots confirm that step 4 passed on the Mac and was
committed locally as `9ee09bc`, with a clean working tree. This step-5
update was checked here on Linux; the supplied commands repeat its
checks on the Mac before committing. No GitHub publication or Actions
run was performed.


# Step 6 — Farey separation and upper counting

Validated on 18 September 2026 in Linux x86_64 with the same pinned
Lean 4.24.0 and mathlib v4.24.0 revisions. No dependency update was made.
The reference manuscript and its SHA-256 remain as recorded in step 2.

- `lake build`: passed, 2408 jobs.
- All thirteen source modules passed with `warningAsError=true`.
- `bash scripts/check.sh`: exit code 0.
- The audit includes all 55 explicitly declared project theorems,
  including the nine new results.
- Every new theorem depends only on `propext`, `Classical.choice`,
  and `Quot.sound`.
- No listed theorem depends on `sorryAx` or an additional project axiom.

New modules: `FareySeparation.lean`, `FareyCounting.lean`.
They prove the strict spacing for rationals with denominators below 2Q,
the one-interval packing bound, the one-source-per-short-cell corollary,
and the Lebesgue-volume bound 4Q^2 |E| + R for a finite rational set
covered by at most R supplied disjoint intervals. The real-valued bound
requires finite volume; its extended-real version also covers unbounded
intervals. An interval decomposition is an explicit input, not constructed
from an overlapping cover or from analytic sublevel data.

The extra precompiled measure-theory dependencies were obtained with:

```bash
lake exe cache get Mathlib.MeasureTheory.Measure.Lebesgue.Basic
```

These are upper estimates proved without any counting hypothesis.
They do not prove the lower source-supply estimate of Lemma 2.2 and
do not yet supply `HasUniformDangerBound` for Proposition 5.1.
Theorems 1.1 and 1.2 are not fully formalized.

The user's terminal output confirms that step 5 was committed on the
Mac as `87baa5a`, with a clean working tree; the preceding screenshot
confirms its successful check. This step-6 update was tested here on
Linux; the supplied commands repeat its checks on the Mac before
committing. No GitHub publication or Actions run was performed.


# Step 7 — unconditional Farey source supply

Validated on 18 September 2026 in Linux x86_64 with the same pinned
Lean 4.24.0 and mathlib v4.24.0 revisions. The manuscript SHA-256 remains
`4ac94b1f36e6a48103b25344e8e736657cef2cb5944c600c5afe098119f8b995`.

- `lake build`: passed, 2422 jobs.
- All 17 project source modules passed with `warningAsError=true`.
- `bash scripts/check.sh`: exit code 0.
- All 81 named theorems have exactly one entry in `scripts/Audit.lean`.
- The audit for all 81 theorems uses only `propext`, `Classical.choice`,
  and `Quot.sound`; no `sorryAx` or additional project axiom occurs.
- The 26 new declarations are unconditional finite arithmetic results,
  the source-supply theorem, and an escape theorem conditional on the
  remaining explicit analytic/counting inputs.
- The four new modules contain no `sorry`, `admit`, custom axiom, or
  `native_decide`.
- `sourceFractions_quarter_supply` and `exists_source_supply_threshold`
  match Lemma 2.2: all real l<u, exact reduced denominator block [Q,2Q),
  absolute constant 1/4, and an interval-dependent natural threshold.
- `UniformCountingInputs.toFusionInputs` installs the proved supply;
  `exists_escape_of_uniform_counting` no longer assumes rational supply.

Additional mathlib cache modules were fetched with:

```bash
lake exe cache get Mathlib.NumberTheory.ArithmeticFunction Mathlib.Data.Nat.Totient
```

The proof replaces the manuscript's classical summatory asymptotics with
explicit elementary bounds. It does not claim the asymptotic 9/pi^2,
and does not prove Proposition 5.1 or the main analytic theorems.
See `docs/STEP7_PT.md` for the estimates and exact remaining hypotheses.

## GitHub state at preparation of this patch

The user confirmed step 6 as commit `c47dc2c`. The private repository
`DiegoMarquesMath/MahlerLean` was then created from the Mac with all six
commits. The user supplied the successful GitHub Actions output for run
35382425028, including build and audit (7m55s):
https://github.com/DiegoMarquesMath/MahlerLean/actions/runs/35382425028

That remote success applies to step 6, not to this step-7 update.
The current session's GitHub connection remains authenticated as DiegoNash
and a repository metadata request returned 404. This step has therefore
been checked locally and packaged for application, commit and push from
the user's Mac. Its remote build is still to be confirmed after the push.

# Step 8 — analytic zeros and Wronskian localization

Validated on 18 September 2026 in Linux x86_64 with the same pinned
Lean 4.24.0 and mathlib v4.24.0 revisions. No dependency update was made.
The manuscript SHA-256 remains
`4ac94b1f36e6a48103b25344e8e736657cef2cb5944c600c5afe098119f8b995`.

- `lake build`: passed, 2430 jobs.
- All 20 project modules passed with `warningAsError=true`.
- `bash scripts/check.sh`: exit code 0.
- All 96 named project theorems have exactly one entry in the audit.
- All 96 printed dependency lists contain only `propext`,
  `Classical.choice`, and `Quot.sound`; no `sorryAx` or project axiom.
- The 15 new theorem statements were reviewed for their explicit
  analyticity, compactness, domain and nontriviality hypotheses.
- The Wronskian has derivative orders 0,...,N-1 as rows, and the
  rational family has precisely 2(d+1) entries in lexicographic order.
- The compact zero set has an exact membership equivalence. The fusion
  set uses degrees 2<=d<=max(2,ceil(10(n+3)/97)), and is nested.
- The new adapter supplies finite forbidden sets and differentiability;
  it preserves the original uniform dangerous-source counting interface.
- No manuscript text, existing theorem statement or pinned dependency
  revision was changed.

The three new modules are `AnalyticLocalization.lean`,
`WronskianLocalization.lean`, and `FusionFromWronskians.lean`.
The proof of analytic zero finiteness uses mathlib's identity theorem
and compact accumulation. Separation follows from the finite-avoidance
lemma and the extreme value theorem. Wronskian analyticity follows from
analytic derivatives and the finite determinant expansion.

**Remaining hypotheses:** W_d is not identically zero (for each relevant
degree), and Proposition 5.1's counting estimate. This step does not prove
these hypotheses from nonrationality, or prove uniform sublevel bounds.
It does not complete Theorems 1.1 or 1.2.

The user confirmed commit `58e6a52` pushed to `origin/main` and GitHub
Actions run 35386107578 completed with success:
https://github.com/DiegoMarquesMath/MahlerLean/actions/runs/35386107578
This confirms step 7. The step-8 patch is locally verified; its Mac check,
commit, push and remote verification remain to be run. The connected
GitHub account was checked again: DiegoNash, with a 404 response for the
private DiegoMarquesMath/MahlerLean repository. No remote write occurred.


# Step 12g — global uniform sublevel measure estimate

Validated on 20 September 2026 by GitHub Actions on the pinned Lean 4.24.0
and mathlib v4.24.0 revisions.

- Workflow run 35479026128 completed successfully:
  https://github.com/DiegoMarquesMath/MahlerLean/actions/runs/35479026128
- `lake build` passed with 3129 jobs.
- `bash scripts/check.sh` passed with warnings treated as errors.
- The zero-order and positive-order patches are assembled with the common
  exponent `1/(N-1)`.
- The compact coefficient/source cover is clipped to the fixed source
  interval and yields a global measure estimate uniform over all unit
  coefficient vectors.
- No `sorry`, `admit`, custom axiom, or placeholder was introduced.

The uniform bound on the number of interval components and the
rational-family specialization remain to finish Step 12.


# Step 12 — uniform analytic sublevel theorem

The new modules are `SublevelIntervals`, `UniformSublevelIntervals`, and
`UniformSublevel`. The root module imports all three transitively, and
`scripts/Audit.lean` includes all seven new named theorems (182 entries total).
Lean and mathlib revisions are unchanged.

The complete build, including the rational-family specialization, passed
in run 35482382760 at commit `70c8457` (3132 jobs). That run's strict audit
stopped on three deprecated-name warnings. These have been replaced with
`Finset.notMem_empty`; the branch's subsequent CI is the verification gate
for the corrected sources. A successful build alone is not an audit pass.

The audited statements require analyticity on an open neighborhood and a
nonvanishing Wronskian on the compact source interval. They quantify the
positive measure constant, interval bound, and smallness threshold before
all unit coefficient vectors and sublevel heights. The interval union is
exact, includes singleton pieces, and may overlap. The general C^(N-1)
version of Lemma 3.5 is not claimed. See `docs/STEP12_PT.md` for the remaining
Farey interface, nonrationality, determinant, and final-theorem dependencies.

# Step 13 — arithmetic determinant lower bounds

Validated on 20 September 2026 at commit
`a6aa168d41a421f2dbecc51d98a3a670a931b60d` by
[GitHub Actions run 35486318942](https://github.com/DiegoMarquesMath/MahlerLean/actions/runs/35486318942).

- Full build passed (3133 jobs).
- All project modules passed with warnings treated as errors.
- All 188 listed declarations were printed by the axiom audit.
- Every printed list contains only `propext`, `Classical.choice`, and `Quot.sound`.
- The six new theorems cover integral row scaling, exact denominator
  clearing, product and dyadic lower bounds, and determinant vanishing
  below the arithmetic threshold.
- Fractions need not be reduced; arbitrary signed numerators and degree
  zero are included. Positive denominators are explicit hypotheses.
- The analytic upper bound remains to be proved; its strict comparison
  with the arithmetic threshold is a hypothesis of the vanishing theorem.
- No manuscript or dependency revision was changed.

The record above concerns the exact Lean source at the cited commit.
Subsequent documentation-only commits do not change that source.
# Step 13 — analytic determinant groundwork

Validated on 20 September 2026 at commit
`8ebbe3fe055d6a9d6224f54af8838dee4fdc8fca` by
[GitHub Actions run 35487464974](https://github.com/DiegoMarquesMath/MahlerLean/actions/runs/35487464974).

- Full build passed (3134 jobs).
- The listed-theorem audit passed for 196 declarations.
- The eight new theorems depend only on `propext`, `Classical.choice`,
  and `Quot.sound`; no `sorryAx` or custom axiom appears.
- The module proves determinant bounds from row L¹ sizes, exact vertical
  perturbation coordinates, their L¹ bound, and the exponent identity used
  in the perturbed determinant expansion.
- The complete smooth-curve Taylor determinant estimate remains pending.


# Step 13 — vector Taylor and target-linear perturbations

Validated on 20 September 2026 at commit
`953661b05f47ca3d3645b1ce1b0c72fc149bd031` by
[GitHub Actions run 35488804840](https://github.com/DiegoMarquesMath/MahlerLean/actions/runs/35488804840).

- Full build passed (3139 jobs).
- Warnings were treated as errors.
- The listed-theorem audit passed for 208 declarations.
- The twelve new theorems depend only on `propext`,
  `Classical.choice`, and `Quot.sound`.
- Vector-valued Taylor remainders are uniform on compact intervals and have
  the determinant-dimension form (Cρ^N).
- The target-linear curve is connected exactly to the rows of the evaluation
  matrix and inherits arbitrary finite smoothness from analyticity.
- The exact graph-plus-perturbation decomposition, row L¹ bounds, and the
  all-error determinant term are formalized.
- The mixed multilinear terms and the complete
  (ρ^{N(N-1)/2}) determinant estimate remain pending.


# Step 13 — alternating Taylor and remainder-row expansion

Validated on 20 September 2026 at commit
`8034de7890ad557f2f69037a19afd6ab566626ee` by
[GitHub Actions run 35490297130](https://github.com/DiegoMarquesMath/MahlerLean/actions/runs/35490297130).

- Full build passed (3142 jobs).
- Warnings were treated as errors.
- The listed-theorem audit passed for 224 declarations.
- The eleven declarations added after the previous recorded source milestone
  use only `propext`, `Classical.choice`, and `Quot.sound`.
- Taylor-polynomial determinants are expanded over derivative-order choices;
  non-injective choices vanish by alternation.
- Distinct derivative orders yield the exact triangular exponent
  (N(N-1)/2).
- A canonical finite derivative-determinant constant controls
  `taylorWithinEval` rows of arbitrary positive order.
- The determinant of `P+R` is expanded rowwise, and every term containing
  a small remainder row has an explicit Leibniz bound.
- The final uniform smooth-curve assembly and the simultaneous vertical
  perturbation estimate remain pending.

## Proposition 5.1: complete two-height assembly

The records above describe earlier milestones. The current assembly is
`MahlerLean.proposition_5_1` in `TwoHeightCounting.lean`, with its explicit
analytic, derivative and Wronskian hypotheses. It bounds the original
`dangerousSources`, with the leading constant chosen before the subinterval
and approximation order, and the remainder constant and positive natural
threshold chosen before the target cutoff H.

Validation for this change:
- Compiled `DangerousSourceDecomposition.lean` and `TwoHeightCounting.lean`
  with Lean 4.24.0 and `-DwarningAsError=true`.
- Inspected the printed statement of `proposition_5_1`.
- Audited `exists_dyadic_target_block`, `hasTargetWitness_small_or_large`,
  `proposition_5_1_of_fixed_bounds`, `proposition_5_1`, and
  `proposition_5_1_uniformDangerBound`. Their transitive axiom dependencies
  are exactly `propext, Classical.choice, Quot.sound`; no `sorryAx`.
- This records targeted module compilation and theorem audits, not a new
  full `scripts/check.sh` run or a completed GitHub Actions run.

The final corollary supplies `HasUniformDangerBound`. Theorem 1.2 from the
manuscript's hypotheses is still pending.

## Step 14: manuscript correspondence and analytic fusion

Compared Proposition 5.1 and its preceding definitions in the manuscript
at commit 1cd6a0b2a8692b5278365c34ef60571a5fa48081 with the Lean statement.
See docs/STEP14_PT.md for the correspondence and scope.
Compiled FusionFromTwoHeight.lean with warnings as errors and audited
exists_escape_of_analytic_wronskians: only propext, Classical.choice,
Quot.sound; no sorryAx. The theorem discharges the counting input using
Proposition 5.1. Derivative bounds and Wronskian nontriviality remain
explicit; Theorem 1.2 from nonrationality is not yet claimed.
This records targeted validation, not a completed new full CI run.

## Step 15: derivative localization

Compiled AnalyticDerivativeInterval.lean with warnings as errors.
Audited exists_deriv_ne_zero_of_analytic_nonconstant,
exists_analytic_derivative_interval,
exists_escape_of_nonconstant_analytic_wronskians, and
exists_escape_in_open_of_analytic_wronskians. Only propext,
Classical.choice, Quot.sound occur transitively. The final theorem has
no supplied counting or derivative-bound hypotheses; Wronskian
nontriviality and nonconstancy remain explicit. This is targeted
validation, not a new full CI success claim.

## Step 16: polynomial relations and pole cancellation

Compiled RationalRelation.lean with warnings as errors. Audited
polynomial_eq_zero_on_open, isRationalOn_of_polynomial_relation,
polynomial_relation_eq_zero_of_not_rational, nonconstant_of_not_rational,
and exists_escape_of_not_rational_and_wronskians. Dependencies are only
propext, Classical.choice, Quot.sound. Rationality requires a denominator
nonzero everywhere on U; gcd cancellation and the analytic identity theorem
justify removal of apparent poles. Wronskian nontriviality remains an
explicit hypothesis of escape. The full analytic Wronskian criterion is
not claimed. This records targeted validation, not a new full CI run.
