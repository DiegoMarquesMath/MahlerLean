import MahlerLean.CellCountingAssembly
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Floor.Ring

noncomputable section
namespace MahlerLean

/-- Every admissible dyadic index is in a finite range independent of H. -/
theorem dyadic_index_lt_uniform_count {Q H v : ℝ} (hQ : 2 ≤ Q) (hH : 1 ≤ H)
    {k : ℕ} (hk : (2 : ℝ)^k * H < Q ^ v) :
    k < ⌈v * Real.log Q / Real.log 2⌉₊ := by
  have hQpos : 0 < Q := by linarith
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpow : (2 : ℝ)^k < Q^v := by
    have := mul_le_mul_of_nonneg_left hH (pow_nonneg h2.le k)
    nlinarith
  have hl := Real.log_lt_log (pow_pos h2 k) hpow
  rw [Real.log_pow, Real.log_rpow hQpos] at hl
  apply Nat.lt_ceil.mpr
  exact (lt_div_iff₀ hlog2).mpr hl

/-- Uniform logarithmic bound for the number of possible dyadic blocks. -/
theorem uniform_dyadic_count_le_log {Q v : ℝ} (hQ : 2 ≤ Q) (hv : 0 ≤ v) :
    (⌈v * Real.log Q / Real.log 2⌉₊ : ℝ) ≤
      ((v + 1) / Real.log 2) * Real.log Q := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log 2 ≤ Real.log Q := Real.log_le_log (by norm_num) hQ
  have hl0 : 0 ≤ Real.log Q := hlog2.le.trans hlog
  have hc := (Nat.ceil_lt_add_one (div_nonneg (mul_nonneg hv hl0) hlog2.le)).le
  have h1 : 1 ≤ Real.log Q / Real.log 2 := (le_div_iff₀ hlog2).mpr (by simpa using hlog)
  calc
    (⌈v * Real.log Q / Real.log 2⌉₊ : ℝ) ≤ v * Real.log Q / Real.log 2 + 1 := hc
    _ ≤ v * Real.log Q / Real.log 2 + Real.log Q / Real.log 2 := add_le_add_left h1 _
    _ = _ := by ring

/-- Convert an actual large dyadic height into the adaptive exponent u. -/
theorem large_block_log_exponent {Q B v : ℝ} (hQ : 2 ≤ Q)
    (hlow : Q ^ ((1 : ℝ)/5) ≤ B) (hupp : B < Q ^ v) :
    Q ^ (Real.logb Q B) = B ∧
      (1 : ℝ)/5 ≤ Real.logb Q B ∧ Real.logb Q B < v := by
  have hQ1 : 1 < Q := by linarith
  have hQpos : 0 < Q := by linarith
  have hB : 0 < B := (Real.rpow_pos_of_pos hQpos _).trans_le hlow
  refine ⟨Real.rpow_logb hQpos (ne_of_gt hQ1) hB, ?_, ?_⟩
  · have hh := Real.logb_le_logb_of_le hQ1 (Real.rpow_pos_of_pos hQpos _) hlow
    simpa only [Real.logb_rpow hQpos (ne_of_gt hQ1)] using hh
  · have hh := Real.logb_lt_logb hQ1 hB hupp
    simpa only [Real.logb_rpow hQpos (ne_of_gt hQ1)] using hh

end MahlerLean
