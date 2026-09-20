import MahlerLean.LargeTargetDyadicCounting

open Set
noncomputable section
namespace MahlerLean

/-- Convert the original safety margin to the adaptive large-block error.
The denominator b is the original witness denominator, not its reduction. -/
theorem safetyMargin_le_largeTarget_error {Q A b : ℕ} {M u : ℝ}
    (hQ : (1 : ℝ) ≤ Q) (hM : 0 ≤ M)
    (hb : (Q : ℝ)^u ≤ (b : ℝ)) :
    safetyMargin M Q A b ≤ (2 + 4*M) * (Q : ℝ)^(-largeTargetS A u) := by
  have hQpos : (0 : ℝ) < Q := lt_of_lt_of_le zero_lt_one hQ
  have hpow := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hQpos u) hb
    (by norm_num : -(100 : ℝ) ≤ 0)
  rw [← Real.rpow_mul hQpos.le] at hpow
  have hs1 : largeTargetS A u ≤ 100*u := min_le_left _ _
  have hs2 : largeTargetS A u ≤ (A : ℝ) := min_le_right _ _
  have hp1 := Real.rpow_le_rpow_of_exponent_le hQ (show u * -(100 : ℝ) ≤ -largeTargetS A u by linarith)
  have hp2 := Real.rpow_le_rpow_of_exponent_le hQ (neg_le_neg hs2)
  have hbpow : ((b : ℝ)^100)⁻¹ ≤ (Q : ℝ)^(-largeTargetS A u) := by
    simpa only [Real.rpow_neg (Nat.cast_nonneg b), Real.rpow_ofNat] using hpow.trans hp1
  have hqpow : ((Q : ℝ)^A)⁻¹ ≤ (Q : ℝ)^(-largeTargetS A u) := by
    simpa only [Real.rpow_neg hQpos.le, Real.rpow_natCast] using hp2
  unfold safetyMargin
  nlinarith [mul_le_mul_of_nonneg_left hqpow (show 0 ≤ 4*M by positivity)]

/-- Reducing a target witness can only decrease its denominator. -/
theorem witness_rational_den_le (a : ℤ) {b : ℕ} (hb : 0 < b) :
    (Rat.divInt a b).den ≤ b := by
  rw [Rat.den_divInt]
  simp only [Int.natCast_eq_zero, Nat.ne_of_gt hb, ↓reduceIte, Int.natAbs_natCast]
  exact Nat.div_le_self _ _

/-- The full large-target contribution with the manuscript's original margin. -/
theorem exists_largeTarget_original_margin_card_bound
    {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hf : AnalyticOnNhd ℝ f U) (A : ℕ)
    {a b M : ℝ} (hab : a < b) (hI : Icc a b ⊆ U) (hM : 0 ≤ M)
    (hW : ∀ d : ℕ, 2 ≤ d → d ≤ wronskianDegreeCutoff A →
      ∀ z ∈ Icc a b, rationalWronskian f d z ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∃ Q₀ : ℝ, 2 ≤ Q₀ ∧
      ∀ Q : ℕ, Q₀ ≤ (Q : ℝ) → ∀ H : ℝ, 1 ≤ H → ∀ S : Finset ℚ,
        (∀ r ∈ S, r.den < 2 * Q) →
        (∀ r ∈ S, (r : ℝ) ∈ Icc a b) →
        (∀ r ∈ S, ∃ k : ℕ,
          (Q : ℝ) ^ ((1 : ℝ)/5) ≤ (2 : ℝ)^k * H ∧
          (2 : ℝ)^k * H < (Q : ℝ) ^ ((A : ℝ)/97) ∧
          ∃ p : ℤ, ∃ q : ℕ, 0 < q ∧
            (2 : ℝ)^k * H ≤ (q : ℝ) ∧ (q : ℝ) < 2 * ((2 : ℝ)^k * H) ∧
            |f r - (p : ℝ) / q| ≤ safetyMargin M Q A q) →
        (S.card : ℝ) ≤ C * (Q : ℝ) ^ ((17 : ℝ)/10) := by
  obtain ⟨C, hC, Q₀, hQ₀, hcount⟩ :=
    exists_largeTarget_dyadic_card_bound hU hf A hab hI
      (show 0 ≤ 2 + 4*M by positivity) hW
  refine ⟨C, hC, Q₀, hQ₀, ?_⟩
  intro Q hQ H hH S hden hx hw
  apply hcount Q hQ H hH S hden hx
  intro r hr
  obtain ⟨k, hklo, hkhi, p, q, hq, hqlo, hqhi, herr⟩ := hw r hr
  refine ⟨k, hklo, hkhi, Rat.divInt p q, ?_, ?_⟩
  · have hrat : ((Rat.divInt p q).den : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast witness_rational_den_le p hq
    exact hrat.trans hqhi.le
  · have hQ2 : (2 : ℝ) ≤ Q := hQ₀.trans hQ
    obtain ⟨hBu, _, _⟩ := large_block_log_exponent hQ2 hklo hkhi
    have hmargin := safetyMargin_le_largeTarget_error (A := A)
      (show (1 : ℝ) ≤ Q by linarith) hM
      (u := Real.logb (Q : ℝ) ((2 : ℝ)^k * H))
      (by simpa only [hBu] using hqlo)
    have he := herr.trans hmargin
    simpa only [Rat.cast_divInt, Int.cast_natCast, abs_sub_comm] using he

end MahlerLean
