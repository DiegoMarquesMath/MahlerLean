import MahlerLean.SmallTargetWitnessBox
import MahlerLean.LargeTargetSafetyMargin

namespace MahlerLean

theorem safetyMargin_le_two_add_four {M : ℝ} {Q A q : ℕ}
    (hM : 0 ≤ M) (hQ : 0 < Q) (hq : 0 < q) :
    safetyMargin M Q A q ≤ 2+4*M := by
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have h1 : ((q : ℝ)^100)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hq1)
  have h2 : ((Q : ℝ)^A)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hQ1)
  unfold safetyMargin
  nlinarith [mul_le_mul_of_nonneg_left h2 (show 0 ≤ 4*M by positivity)]

theorem target_witness_numerator_bound {f : ℝ → ℝ} {x F M : ℝ} {Q A q : ℕ} {p : ℤ}
    (hM : 0 ≤ M) (hQ : 0 < Q) (hq : 0 < q) (hF : |f x| ≤ F)
    (herr : |f x-(p : ℝ)/q| ≤ safetyMargin M Q A q) :
    |(p : ℝ)| ≤ (F+2+4*M)*q := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have htri := abs_add_le (f x) ((p : ℝ)/q-f x)
  rw [add_sub_cancel, abs_sub_comm ((p : ℝ)/q)] at htri
  have hh : |(p : ℝ)/q| ≤ F+2+4*M := by
    linarith [safetyMargin_le_two_add_four (A := A) hM hQ hq]
  rw [abs_div, abs_of_pos hqpos] at hh
  exact (div_le_iff₀ hqpos).mp hh

theorem safetyMargin_le_block {M B : ℝ} {Q A q : ℕ}
    (hB : 0 < B) (hq : B ≤ (q : ℝ)) :
    safetyMargin M Q A q ≤ 2*(B^100)⁻¹+4*M*((Q : ℝ)^A)⁻¹ := by
  have hp : B^100 ≤ (q : ℝ)^100 := pow_le_pow_left₀ hB.le hq _
  have hi := inv_anti₀ (pow_pos hB 100) hp
  unfold safetyMargin
  linarith

end MahlerLean
