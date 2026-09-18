import MahlerLean.CountingToSafeCenter
import Mathlib.Tactic.FieldSimp

/-!
The floor cutoff and the quantitative tail invariant at the next fusion
stage. Integer negative powers are represented as inverses of natural
powers. The scale hypothesis is (Q4), with Q^(-A/97) written as the
inverse of targetCutoff Q A.
-/

namespace MahlerLean

noncomputable section

/-- R = (2Q)^(-A). -/
def fusionRadius (Q A : ℕ) : ℝ := ((2 * (Q : ℝ)) ^ A)⁻¹

/-- The next integer target cutoff. -/
def nextCutoff (Q A : ℕ) : ℕ := ⌊targetCutoff Q A⌋₊

/-- The defining power identity for the two-height cutoff. -/
theorem targetCutoff_pow97 (Q A : ℕ) :
    (targetCutoff Q A) ^ 97 = (Q : ℝ) ^ A := by
  unfold targetCutoff
  rw [← Real.rpow_mul_natCast (Nat.cast_nonneg Q)]
  norm_num only [Nat.cast_ofNat]
  rw [div_mul_cancel₀ _ (by norm_num), Real.rpow_natCast]

/-- Floor loses at most a factor two once the real cutoff is at least two. -/
theorem half_le_nat_floor (X : ℝ) (hX : 2 ≤ X) :
    X / 2 ≤ (⌊X⌋₊ : ℝ) := by
  have := Nat.lt_floor_add_one X
  linarith

/-- The integer cutoff never exceeds its real counterpart. -/
theorem nextCutoff_le_targetCutoff (Q A : ℕ) :
    (nextCutoff Q A : ℝ) ≤ targetCutoff Q A := by
  exact Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg Q) _)

/-- Condition (Q3) gives strict growth of the integer cutoffs. -/
theorem nextCutoff_gt (Q A H : ℕ)
    (hheight : 2 * (H : ℝ) + 2 ≤ targetCutoff Q A) :
    H < nextCutoff Q A := by
  have hcast : ((2 * H + 2 : ℕ) : ℝ) ≤ targetCutoff Q A := by
    exact_mod_cast hheight
  have hfloor : 2 * H + 2 ≤ nextCutoff Q A := Nat.le_floor hcast
  omega

/-- The fusion radius is no larger than q^(-A) for q <= 2Q. -/
theorem fusionRadius_le_source_accuracy (Q q A : ℕ)
    (hq : 0 < q) (hbound : q ≤ 2 * Q) :
    fusionRadius Q A ≤ ((q : ℝ) ^ A)⁻¹ := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hboundR : (q : ℝ) ≤ 2 * (Q : ℝ) := by exact_mod_cast hbound
  simpa only [fusionRadius, one_div] using
    one_div_le_one_div_of_le (pow_pos hqR A)
      (pow_le_pow_left₀ hqR.le hboundR A)

/-- The floor cutoff satisfies T^(-98) <= 2^98 X^(-98), where X = T(Q,A). -/
theorem nextCutoff_tail_le (Q A : ℕ) (hX : 2 ≤ targetCutoff Q A) :
    (((nextCutoff Q A : ℕ) : ℝ) ^ 98)⁻¹ ≤
      (2 : ℝ) ^ 98 * ((targetCutoff Q A) ^ 98)⁻¹ := by
  have hXpos : 0 < targetCutoff Q A := by linarith
  have hhalf := half_le_nat_floor (targetCutoff Q A) hX
  have hpow : (targetCutoff Q A / 2) ^ 98 ≤ ((nextCutoff Q A : ℕ) : ℝ) ^ 98 :=
    pow_le_pow_left₀ (by positivity) hhalf 98
  have hinv := one_div_le_one_div_of_le (pow_pos (by positivity : 0 < targetCutoff Q A / 2) 98) hpow
  have heq : 1 / (targetCutoff Q A / 2) ^ 98 =
      (2 : ℝ) ^ 98 * ((targetCutoff Q A) ^ 98)⁻¹ := by
    rw [div_pow]
    field_simp
  simpa only [heq, one_div] using hinv

/-- Condition (Q4) propagates the tail smallness invariant at the next
middle third, whose length is R/(3 Lambda). -/
theorem tail_smallness_next (Q A Lambda : ℕ) (Clow cF : ℝ)
    (hQ : 0 < Q) (hLambda : 0 < Lambda) (hC : 0 ≤ Clow)
    (hX : 2 ≤ targetCutoff Q A)
    (hscale : 3 * Clow * (Lambda : ℝ) * (2 : ℝ) ^ (A + 98) *
      (targetCutoff Q A)⁻¹ ≤ cF / 4) :
    Clow * (((nextCutoff Q A : ℕ) : ℝ) ^ 98)⁻¹ ≤
      (cF / 4) * (fusionRadius Q A / (3 * (Lambda : ℝ))) := by
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hLpos : (0 : ℝ) < Lambda := by exact_mod_cast hLambda
  have hXpos : 0 < targetCutoff Q A := Real.rpow_pos_of_pos hQpos _
  have hRpos : 0 < fusionRadius Q A := by unfold fusionRadius; positivity
  have hX98 : (targetCutoff Q A) ^ 98 = (Q : ℝ) ^ A * targetCutoff Q A := by
    rw [show 98 = 97 + 1 from rfl, pow_succ, targetCutoff_pow97]
  have hid : (3 * Clow * (Lambda : ℝ) * (2 : ℝ) ^ (A + 98) *
      (targetCutoff Q A)⁻¹) * (fusionRadius Q A / (3 * (Lambda : ℝ))) =
      Clow * ((2 : ℝ) ^ 98 * ((targetCutoff Q A) ^ 98)⁻¹) := by
    rw [hX98, fusionRadius, mul_pow, pow_add]
    field_simp
  calc
    Clow * (((nextCutoff Q A : ℕ) : ℝ) ^ 98)⁻¹
      ≤ Clow * ((2 : ℝ) ^ 98 * ((targetCutoff Q A) ^ 98)⁻¹) :=
        mul_le_mul_of_nonneg_left (nextCutoff_tail_le Q A hX) hC
    _ = (3 * Clow * (Lambda : ℝ) * (2 : ℝ) ^ (A + 98) *
        (targetCutoff Q A)⁻¹) * (fusionRadius Q A / (3 * (Lambda : ℝ))) := hid.symm
    _ ≤ (cF / 4) * (fusionRadius Q A / (3 * (Lambda : ℝ))) :=
      mul_le_mul_of_nonneg_right hscale (by positivity)

/-- All scale requirements can be met simultaneously, after the interval
margin, target cutoff and forbidden-set size have been fixed. The minimum
height can incorporate the counting threshold and previous denominators. -/
theorem exists_large_fusion_scale (A H Lambda Qmin : ℕ) (Clow cF delta : ℝ)
    (hA : 0 < A) (hcF : 0 < cF) (hdelta : 0 < delta) :
    ∃ Q : ℕ, Qmin ≤ Q ∧ 2 ≤ Q ∧ fusionRadius Q A < delta ∧
      2 * (H : ℝ) + 2 ≤ targetCutoff Q A ∧
      3 * Clow * (Lambda : ℝ) * (2 : ℝ) ^ (A + 98) *
        (targetCutoff Q A)⁻¹ ≤ cF / 4 := by
  have hAR : (0 : ℝ) < A := by exact_mod_cast hA
  have hpow : Filter.Tendsto (fun Q : ℕ => ((Q : ℝ) ^ A)⁻¹)
      Filter.atTop (nhds 0) := by
    simpa only [Function.comp_def, Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_natCast] using
      (tendsto_rpow_neg_atTop hAR).comp tendsto_natCast_atTop_atTop
  have hXtop : Filter.Tendsto (fun Q : ℕ => targetCutoff Q A)
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (div_pos hAR (by norm_num))).comp tendsto_natCast_atTop_atTop
  have hscaled : Filter.Tendsto
      (fun Q : ℕ => 3 * Clow * (Lambda : ℝ) * (2 : ℝ) ^ (A + 98) *
        (targetCutoff Q A)⁻¹) Filter.atTop (nhds 0) := by
    simpa using hXtop.inv_tendsto_atTop.const_mul
      (3 * Clow * (Lambda : ℝ) * (2 : ℝ) ^ (A + 98))
  have hsmall := hpow.eventually_lt_const hdelta
  have hheight := hXtop.eventually_ge_atTop (2 * (H : ℝ) + 2)
  have htail := hscaled.eventually_le_const (show (0 : ℝ) < cF / 4 by positivity)
  have hall : ∀ᶠ Q : ℕ in Filter.atTop,
      Qmin ≤ Q ∧ 2 ≤ Q ∧ fusionRadius Q A < delta ∧
      2 * (H : ℝ) + 2 ≤ targetCutoff Q A ∧
      3 * Clow * (Lambda : ℝ) * (2 : ℝ) ^ (A + 98) *
        (targetCutoff Q A)⁻¹ ≤ cF / 4 := by
    filter_upwards [Filter.eventually_ge_atTop Qmin,
      Filter.eventually_ge_atTop (2 : ℕ), hsmall, hheight, htail]
      with Q hmin htwo hrad hhigh hbudget
    exact ⟨hmin, htwo,
      lt_of_le_of_lt (fusionRadius_le_source_accuracy Q Q A (by omega) (by omega)) hrad,
      hhigh, hbudget⟩
  exact hall.exists

end
end MahlerLean
