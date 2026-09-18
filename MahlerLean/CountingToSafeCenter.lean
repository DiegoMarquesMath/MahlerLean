import MahlerLean.RationalBlocks
import MahlerLean.SafeCenter
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
The implication from the two counting estimates to Lemma 6.1.

The source-supply bound (Lemma 2.2) and the dangerous-center bound
(Proposition 5.1) are explicit hypotheses, not project axioms and not
results proved in this file. The final threshold is chosen before H,
retaining the uniformity in the lower target cutoff.
-/

namespace MahlerLean

open Filter Topology

/-- Any fixed subquadratic real power is eventually smaller than one
quarter of a positive quadratic supply. -/
theorem eventually_subquadratic_quarter (C c p : ℝ) (hc : 0 < c) (hp : p < 2) :
    ∃ Q₁ : ℕ, ∀ Q : ℕ, Q₁ ≤ Q →
      C * (Q : ℝ) ^ p ≤ c * (Q : ℝ) ^ 2 / 4 := by
  have hlim : Tendsto (fun Q : ℕ => C * (Q : ℝ) ^ (-(2 - p)))
      atTop (𝓝 0) := by
    simpa using
      ((tendsto_rpow_neg_atTop (sub_pos.mpr hp)).comp
        tendsto_natCast_atTop_atTop).const_mul C
  have hsmall := hlim.eventually_le_const (show (0 : ℝ) < c / 4 by positivity)
  apply eventually_atTop.mp
  filter_upwards [hsmall, eventually_ge_atTop (1 : ℕ)] with Q hQ hQpos
  have hpos : (0 : ℝ) < Q := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hQpos)
  have hratio : C * (Q : ℝ) ^ (-(2 - p)) =
      C * (Q : ℝ) ^ p / (Q : ℝ) ^ 2 := by
    rw [show -(2 - p) = p - 2 by ring, Real.rpow_sub hpos, Real.rpow_two]
    ring
  rw [hratio] at hQ
  have hbound := (div_le_iff₀ (sq_pos_of_pos hpos)).mp hQ
  nlinarith

/-- The positive proportion of source rationals required from Lemma 2.2.
This definition records a hypothesis; it does not prove the supply estimate. -/
def HasSourceSupply (l u cF : ℝ) : Prop :=
  ∃ Q₀ : ℕ, ∀ Q : ℕ, Q₀ ≤ Q →
    cF * (u - l) * (Q : ℝ) ^ 2 ≤ (sourceFractions l u Q).card

/-- The counting conclusion required from Proposition 5.1 on a fixed
interval and at fixed A. Q₀ and C are chosen independently of H.
This definition records a hypothesis; it does not prove Proposition 5.1. -/
def HasUniformDangerBound (f : ℝ → ℝ) (l u M Clow C : ℝ) (A : ℕ) : Prop :=
  ∃ Q₀ : ℕ, ∀ H : ℕ, 2 ≤ H → ∀ Q : ℕ, Q₀ ≤ Q →
    (dangerousSources f l u M Q A H).card ≤
      Clow * (Q : ℝ) ^ 2 * ((H : ℝ) ^ 98)⁻¹ + C * (Q : ℝ) ^ ((17 : ℝ) / 10)

/-- Selection at a single scale after both quarter-budget inequalities
have been established. -/
theorem exists_safeCenter_of_quarter_bounds
    (f : ℝ → ℝ) (l u M c Clow C : ℝ) (Q A H : ℕ)
    (hc : 0 < c) (hQ : 0 < Q)
    (hsupply : c * (Q : ℝ) ^ 2 ≤ (sourceFractions l u Q).card)
    (hdanger : (dangerousSources f l u M Q A H).card ≤
      Clow * (Q : ℝ) ^ 2 * ((H : ℝ) ^ 98)⁻¹ + C * (Q : ℝ) ^ ((17 : ℝ) / 10))
    (htail : Clow * ((H : ℝ) ^ 98)⁻¹ ≤ c / 4)
    (hrem : C * (Q : ℝ) ^ ((17 : ℝ) / 10) ≤ c * (Q : ℝ) ^ 2 / 4) :
    ∃ r ∈ sourceFractions l u Q, IsSafeCenter f M Q A H r := by
  have hQreal : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hpos : 0 < c * (Q : ℝ) ^ 2 := mul_pos hc (sq_pos_of_pos hQreal)
  have hmain : Clow * (Q : ℝ) ^ 2 * ((H : ℝ) ^ 98)⁻¹ ≤
      c * (Q : ℝ) ^ 2 / 4 := by
    nlinarith [mul_le_mul_of_nonneg_right htail (sq_nonneg (Q : ℝ))]
  have hbudget := counting_budget _ _ _ hpos hmain hrem
  have hcardReal : ((dangerousSources f l u M Q A H).card : ℝ) <
      (sourceFractions l u Q).card := lt_of_le_of_lt hdanger (lt_of_lt_of_le hbudget hsupply)
  have hcard : (dangerousSources f l u M Q A H).card <
      (sourceFractions l u Q).card := by exact_mod_cast hcardReal
  obtain ⟨r, hr, hnot⟩ := exists_safe_center (sourceFractions l u Q)
    (dangerousSources f l u M Q A H) hcard
  exact ⟨r, hr, (isSafeCenter_iff_not_mem_dangerousSources f l u M Q A H r hr).mpr hnot⟩

/-- Lemma 6.1 conditional on the two explicit counting inputs.
There is a common source threshold Q₁ for every admissible H satisfying
the tail inequality. The conclusion uses canonical reduced denominators
and covers every target numerator, with no target coprimality condition. -/
theorem safe_center_of_counting_estimates
    (f : ℝ → ℝ) (l u M cF Clow C : ℝ) (A : ℕ)
    (hinterval : l < u) (hcF : 0 < cF)
    (hsupply : HasSourceSupply l u cF)
    (hcount : HasUniformDangerBound f l u M Clow C A) :
    ∃ Q₁ : ℕ, 2 ≤ Q₁ ∧ ∀ H : ℕ, 2 ≤ H →
      Clow * ((H : ℝ) ^ 98)⁻¹ ≤ cF * (u - l) / 4 →
      ∀ Q : ℕ, Q₁ ≤ Q →
      ∃ r : ℚ, l ≤ (r : ℝ) ∧ (r : ℝ) ≤ u ∧
        Q ≤ r.den ∧ r.den < 2 * Q ∧ IsSafeCenter f M Q A H r := by
  obtain ⟨Qs, hs⟩ := hsupply
  obtain ⟨Qd, hd⟩ := hcount
  have hc : 0 < cF * (u - l) := mul_pos hcF (sub_pos.mpr hinterval)
  obtain ⟨Qr, hrem⟩ := eventually_subquadratic_quarter C (cF * (u - l))
    ((17 : ℝ) / 10) hc (by norm_num)
  refine ⟨max 2 (max Qs (max Qd Qr)), by omega, ?_⟩
  intro H hH htail Q hQ
  obtain ⟨r, hr, hsafe⟩ := exists_safeCenter_of_quarter_bounds
    f l u M (cF * (u - l)) Clow C Q A H hc (by omega)
    (hs Q (by omega)) (hd H hH Q (by omega)) htail (hrem Q (by omega))
  obtain ⟨hl, hu, hdenlo, hdenhi⟩ := (mem_sourceFractions l u Q r).mp hr
  exact ⟨r, hl, hu, hdenlo, hdenhi, hsafe⟩

/-- Transfer of all target exclusions from a safe center to a nearby
function value. A later step must derive hmove from the derivative bound. -/
theorem safeCenter_avoidance_of_movement
    (f : ℝ → ℝ) (M : ℝ) (Q A H : ℕ) (r : ℚ) (x : ℝ)
    (hM : 0 ≤ M) (hsafe : IsSafeCenter f M Q A H r)
    (hmove : |f x - f (r : ℝ)| ≤ M * ((Q : ℝ) ^ A)⁻¹) :
    ∀ a : ℤ, ∀ b : ℕ, 0 < b → H ≤ b → (b : ℝ) < targetCutoff Q A →
      ((b : ℝ) ^ 100)⁻¹ < |f x - (a : ℝ) / (b : ℝ)| := by
  intro a b hb hH hT
  apply safety_transfer (f (r : ℝ)) (f x) ((a : ℝ) / (b : ℝ))
    (((b : ℝ) ^ 100)⁻¹) (M * ((Q : ℝ) ^ A)⁻¹)
    (by positivity) (by positivity) ?_ hmove
  simpa only [safetyMargin, mul_assoc] using hsafe a b hb hH hT

end MahlerLean
