# Mathematical roadmap

Reference: Mahler_Question_18SEPT.pdf. Keep this version fixed while matching
statements, and record any later change of the manuscript explicitly.

## Current verified milestone

Step 2 proves safe-center selection conditional on the source supply and
the uniform counting estimate, with a source threshold independent of H.
See [STEP2_PT.md](STEP2_PT.md).

Step 3 proves equivalence between the library and manuscript Liouville
conventions, coverage by the target blocks, and the existence of a
Liouville escape point conditional on the explicit invariants in
`FusionData`. It also derives the movement bound from a derivative bound
using the mean-value theorem. See [STEP3_PT.md](STEP3_PT.md).

Step 4 proves quantitative avoidance of a finite set, simultaneous scale
selection, the floor-cutoff estimates, propagation of the tail bound, and
one successor step from the counting hypotheses on the middle third.
The finite forbidden set and all scale thresholds are fixed before Q is
chosen. See [STEP4_PT.md](STEP4_PT.md).

Step 5 initializes the interval and target cutoff, constructs the infinite
sequence by recursion, and proves all seven fusion invariants from the
explicit `FusionInputs` interface. It also proves uniqueness of the common
point, unbounded source denominators and the counting-to-escape theorem.
See [STEP5_PT.md](STEP5_PT.md).

Step 6 proves rational separation and the upper bound in the component
form of Lemma 2.1: a finite set of rationals in a supplied decomposition
into at most R disjoint intervals has cardinality at most 4Q^2 |E| + R.
The volume is Lebesgue measure; the component term has no factor Q.
See [STEP6_PT.md](STEP6_PT.md).

Step 7 proves Lemma 2.2 with cF = 1/4 by finite Möbius inversion and
elementary totient/divisor estimates. The new `UniformCountingInputs`
interface removes source supply as an assumption in the escape theorem.
See [STEP7_PT.md](STEP7_PT.md).

Step 8 proves compact finiteness of analytic zeros, analyticity of the exact
Wronskians, simultaneous localization, and the finite nested sets Z_n used
in fusion, conditional on Wronskian nontriviality. The new
`WronskianCountingInputs` adapter constructs those sets instead of taking
an arbitrary finite-set sequence as input. See [STEP8_PT.md](STEP8_PT.md).

The abstract infinite fusion argument is formalized conditionally.
Remaining tasks include deriving Wronskian nontriviality from nonrationality,
sublevel interval decompositions, and
Proposition 5.1 with its dependencies. These must provide `FusionInputs`
from the hypotheses of the manuscript before the main theorems can be
claimed as fully formalized.

## Stage 0: reproducible environment

Install VS Code, Lean 4 extension, Elan, and Git. Open the project root;
obtain the matching mathlib cache; build; inspect the nine initial statements.
Make a first local commit. Run the GitHub workflow when the project is published.

## Stage 1: source and target definitions

Inspect mathlib's existing `Liouville` definitions and prove the equivalence
with the convention used in the paper. Do not silently replace the paper's
strict nonzero approximation condition with a weaker definition.

In the pinned v4.24.0 source, this definition is in
`Mathlib/NumberTheory/Transcendental/Liouville/Basic.lean`:
`∀ n : ℕ, ∃ a b : ℤ, 1 < b ∧ x ≠ a / b ∧ |x - a / b| < 1 / (b : ℝ)^n`.
It uses existence at every exponent, while the manuscript states infinitely
many pairs at every exponent. Their equivalence must be explicitly checked.

Specify source fractions in lowest terms, their denominator block [Q, 2Q),
and target witnesses with unreduced denominator allowed. Count distinct
source rationals, not source-target witness pairs. Establish finiteness on
a bounded source interval before using finite cardinalities.

Define the avoidance property for every integer numerator and all sufficiently
large positive target denominators. At first, this explicit inequality can be
used instead of formalizing the irrationality exponent itself.

## Stage 2: abstract fusion, then its application

State all earlier results used by fusion as explicit hypotheses of a
conditional theorem. Do not introduce an axiom asserting Proposition 5.1.

The following parts are now proved under the explicit `FusionInputs`
interface (steps 2--5):

1. Selection of a safe center from supply and exclusion estimates.
2. Stability under movement away from the center.
3. Extraction of an interval of controlled length after deleting finitely
   many Wronskian zeros and the current center.
4. The full simultaneous induction (F1)--(F7), with Q chosen after all
   quantities on which its lower threshold depends.
5. Existence and uniqueness of the point in nested nonempty compact intervals.
6. Unbounded reduced source denominators and arbitrarily strong nonzero
   rational approximations.
7. Coverage of every sufficiently large target denominator by consecutive
   integer blocks [T_n, T_(n+1)).
8. The eventual lower bound for target approximation.

The counting-to-fusion interface must retain both uniformities:
`C_low` independent of the shrinking source interval, and
`C(J,A), Q0(J,A)` independent of H. Include the separate rational supply
and Wronskian localization hypotheses; the numeric inequality alone is not
the full interface.

## Stage 3: Proposition 5.1 and dependencies

Farey separation, the upper estimate from a disjoint interval
decomposition, and rational supply with cF = 1/4 are now proved.
Localized Wronskian separation is now proved given nontriviality.
Remaining statements include rationality versus linear dependence, the analytic
Wronskian criterion, uniform sublevel length and component bounds, determinant perturbation, rational
denominator clearing, rank deficiency and coefficient normalization.

In the large-target range track:

- A >= 20, u >= 1/5, d = ceil(10u), N = 2(d+1).
- kappa <= 33/20, s - kappa*N >= 1/5, s/(N-1) >= 97/35.
- Constants chosen over the finite degree range before Q and target blocks.
- One target witness per source center, all maximal minors, then a relation
  valid for every selected center in the cell.
- Uniformity in normalized polynomial coefficients and number of components.
- Summation of O(log Q) blocks with the exponent loss 1/20.

An obstacle can be missing Lean infrastructure or a mathematical gap.
Record which one it is. Never weaken the final statement just to compile.

## Stage 4: main conclusions and public release

Combine the unconditional estimate with fusion, prove the local rigidity
corollary, and then the entire-function consequence. Audit the exact
formal statements against Theorems 1.2 and 1.1. The independent Section 7
results are a separate milestone.

Only after verification, create a tagged release and describe its precise
scope in the paper. A public blueprint site and an archival DOI can be added
then. A Markdown dependency plan is not itself a machine-checked proof.
