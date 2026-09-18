import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
Elementary parameter calculations from Mahler_Question_18SEPT.pdf.
These calculations do not prove Proposition 5.1 or the fusion theorem.
-/

namespace MahlerLean

/-- The dyadic logarithmic loss used after (5.44). -/
theorem dyadic_exponent_identity :
    (33 : ℚ) / 20 + 1 / 20 = 17 / 10 := by
  norm_num

/-- The remainder exponent in Proposition 5.1 is subquadratic. -/
theorem remainder_exponent_lt_two : (17 : ℚ) / 10 < 2 := by
  norm_num

/-- The Farey exponent gap in (5.42). -/
theorem farey_exponent_gt_two : (2 : ℚ) < 97 / 35 := by
  norm_num

/-- The perturbation gap (5.28), given the preceding exponent estimates. -/
theorem perturbation_gap (s u k N : ℝ)
    (hu : (1 : ℝ) / 5 ≤ u)
    (hs : 97 * u ≤ s)
    (hk : k * N ≤ 96 * u) :
    (1 : ℝ) / 5 ≤ s - k * N := by
  linarith

/-- The exponent identity used to propagate (F7) in (6.26). -/
theorem fusion_exponent_identity (A : ℝ) :
    A - A * (100 - 2) / 97 = -(A / 97) := by
  ring

/-- Strict negativity of that exponent for positive A. -/
theorem fusion_exponent_negative (A : ℝ) (hA : 0 < A) :
    A - A * (100 - 2) / 97 < 0 := by
  rw [fusion_exponent_identity]
  have h : 0 < A / 97 := div_pos hA (by norm_num)
  linarith

end MahlerLean
