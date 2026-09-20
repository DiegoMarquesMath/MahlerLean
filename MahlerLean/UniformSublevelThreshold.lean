import MahlerLean.LargeTargetWitnesses
import MahlerLean.UniformDegreeCounting

noncomputable section
namespace MahlerLean

/-- A common upper bound for the scaled vertical error over all degrees. -/
theorem scaled_error_le_uniform_coefficient {X K δ : ℝ} {d D : ℕ}
    (hX : 1 ≤ X) (hK : 0 ≤ K) (hδ : 0 ≤ δ) (hd : d ≤ D) :
    (2 * (d + 1) : ℕ) * (X ^ d * (K * δ)) ≤
      ((2 * (D + 1) : ℕ) * (X ^ D * K)) * δ := by
  have hN : ((2 * (d + 1) : ℕ) : ℝ) ≤ (2 * (D + 1) : ℕ) := by
    exact_mod_cast (show 2 * (d + 1) ≤ 2 * (D + 1) by omega)
  have hp := pow_le_pow_right₀ hX hd
  calc
    (2 * (d + 1) : ℕ) * (X ^ d * (K * δ)) ≤
      (2 * (D + 1) : ℕ) * (X ^ D * (K * δ)) := by
        exact mul_le_mul hN (mul_le_mul_of_nonneg_right hp (mul_nonneg hK hδ))
          (by positivity) (by positivity)
    _ = _ := by ring

/-- Explicit common sublevel threshold; s ≥ 1 suffices. -/
theorem scaled_error_lt_of_uniform_threshold {Q X K eps s : ℝ} {d D : ℕ}
    (hQ : 1 ≤ Q) (hX : 1 ≤ X) (hK : 0 ≤ K) (heps : 0 < eps)
    (hd : d ≤ D) (hs : 1 ≤ s)
    (hthreshold : ((2 * (D + 1) : ℕ) * (X ^ D * K)) / eps + 1 ≤ Q) :
    (2 * (d + 1) : ℕ) * (X ^ d * (K * Q ^ (-s))) < eps := by
  have hpos : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  let L : ℝ := (2 * (D + 1) : ℕ) * (X ^ D * K)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hLQ : L / eps < Q := by dsimp [L] at *; linarith
  have hLe : L / Q < eps := by
    apply (div_lt_iff₀ hpos).mpr
    have := (div_lt_iff₀ heps).mp hLQ
    nlinarith
  calc
    (2 * (d + 1) : ℕ) * (X ^ d * (K * Q ^ (-s))) ≤ L * Q ^ (-s) :=
      scaled_error_le_uniform_coefficient hX hK (Real.rpow_nonneg hpos.le _) hd
    _ ≤ L * Q ^ (-(1 : ℝ)) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hQ (by linarith)) hL
    _ = L / Q := by rw [Real.rpow_neg_one]; rfl
    _ < eps := hLe

/-- Uniform coefficient absorption in the sublevel power. -/
theorem sublevel_power_le_uniform_decay {Q L E s t : ℝ}
    (hQ : 1 ≤ Q) (hL : 0 ≤ L) (hE : 0 ≤ E)
    (hEL : E ≤ L * Q ^ (-s)) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hst : 2 ≤ s * t) :
    E ^ t ≤ max 1 L * Q ^ (-(2 : ℝ)) := by
  have hpos : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have hM : 1 ≤ max 1 L := le_max_left _ _
  have hcoeff : L ^ t ≤ max 1 L := by
    calc
      L ^ t ≤ (max 1 L) ^ t := Real.rpow_le_rpow hL (le_max_right _ _) ht0
      _ ≤ (max 1 L) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hM ht1
      _ = max 1 L := Real.rpow_one _
  calc
    E ^ t ≤ (L * Q ^ (-s)) ^ t := Real.rpow_le_rpow hE hEL ht0
    _ = L ^ t * Q ^ ((-s) * t) := by
      rw [Real.mul_rpow hL (Real.rpow_nonneg hpos.le _), ← Real.rpow_mul hpos.le]
    _ ≤ max 1 L * Q ^ (-(2 : ℝ)) :=
      mul_le_mul hcoeff (Real.rpow_le_rpow_of_exponent_le hQ (by nlinarith))
        (Real.rpow_nonneg hpos.le _) (by positivity)

/-- The Q squared Farey factor cancels the uniform sublevel decay. -/
theorem farey_sublevel_bound_le_constant {Q C L E s t : ℝ}
    (hQ : 1 ≤ Q) (hC : 0 ≤ C) (hL : 0 ≤ L) (hE : 0 ≤ E)
    (hEL : E ≤ L * Q ^ (-s)) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hst : 2 ≤ s * t) :
    4 * Q ^ 2 * (C * E ^ t) ≤ 4 * C * max 1 L := by
  have hpos : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have hp : Q ^ 2 * Q ^ (-(2 : ℝ)) = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hpos]
    norm_num
  calc
    4 * Q ^ 2 * (C * E ^ t) ≤
      4 * Q ^ 2 * (C * (max 1 L * Q ^ (-(2 : ℝ)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (sublevel_power_le_uniform_decay hQ hL hE hEL ht0 ht1 hst) hC) (by positivity)
    _ = (4 * C * max 1 L) * (Q ^ 2 * Q ^ (-(2 : ℝ))) := by ring
    _ = _ := by rw [hp, mul_one]

end MahlerLean
