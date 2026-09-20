import MahlerLean.UniformDeterminantVanishing

noncomputable section
namespace MahlerLean

/-- A strict power saving absorbs a fixed coefficient with an explicit threshold. -/
theorem strict_power_comparison {Q C α β : ℝ}
    (hQ : 1 ≤ Q) (hC : 0 ≤ C) (hCQ : C < Q) (hgap : β + 1 ≤ α) :
    C * Q ^ (-α) < 1 / Q ^ β := by
  have hpos : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  calc
    C * Q ^ (-α) ≤ C * Q ^ (-(β + 1)) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hQ (by linarith)) hC
    _ < Q * Q ^ (-(β + 1)) :=
      mul_lt_mul_of_pos_right hCQ (Real.rpow_pos_of_pos hpos _)
    _ = 1 / Q ^ β := by
      conv_lhs => lhs; rw [← Real.rpow_one Q]
      rw [← Real.rpow_add hpos]
      have he : (1 : ℝ) + -(β + 1) = -β := by ring
      rw [he, Real.rpow_neg hpos.le, one_div]

/-- The denominator factor is bounded before the adaptive degree is chosen. -/
theorem degree_denominator_factor_le {d D : ℕ} (hd : d ≤ D) :
    (2 : ℝ) ^ (d * (2 * (d + 1)) + 2 * (d + 1)) ≤
      2 ^ (D * (2 * (D + 1)) + 2 * (D + 1)) := by
  apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
  exact Nat.add_le_add (Nat.mul_le_mul hd (by omega)) (by omega)

/-- Exact exponent saving of the manuscript's cell scale. -/
theorem largeTarget_determinant_exponent_gap (u : ℝ) (hu : (1 : ℝ) / 5 ≤ u) :
    ((largeTargetDegree u : ℝ) + u) * largeTargetN u + 1 ≤
      largeTargetKappa u * ((largeTargetN u : ℝ) * (largeTargetN u - 1) / 2) := by
  have hd : (2 : ℝ) ≤ largeTargetDegree u := by
    exact_mod_cast largeTargetDegree_ge_two u hu
  have hden := largeTargetDen_pos u
  rw [largeTargetN_cast]
  unfold largeTargetKappa largeTargetNReal largeTargetDen at *
  field_simp
  nlinarith [sq_nonneg (largeTargetDegree u : ℝ)]

/-- Normalize the two independent denominator heights into a single Q-power. -/
theorem two_height_denominator_eq {Q u : ℝ} (hQ : 0 < Q) (d N : ℕ) :
    (2 * Q) ^ (d * N) * (2 * Q ^ u) ^ N =
      (2 : ℝ) ^ (d * N + N) * Q ^ (((d : ℝ) + u) * N) := by
  rw [mul_pow, mul_pow, pow_add]
  rw [show ((d : ℝ) + u) * N = (d * N : ℕ) + u * N by push_cast; ring]
  rw [Real.rpow_add hQ, Real.rpow_natCast, Real.rpow_mul_natCast hQ.le]
  ring

/-- Explicit strict determinant comparison, uniform in d ≤ D and u.
The only scale hypothesis is a saving of at least one Q-power. -/
theorem determinant_scale_comparison {Q K κ u : ℝ} {d D : ℕ}
    (hQ : 1 ≤ Q) (hK : 0 ≤ K) (hd : d ≤ D)
    (hthreshold : K * 2 ^ (D * (2 * (D + 1)) + 2 * (D + 1)) < Q)
    (hgap : ((d : ℝ) + u) * (2 * (d + 1)) + 1 ≤
      κ * ((2 * (d + 1) : ℕ) : ℝ) * (((2 * (d + 1) : ℕ) : ℝ) - 1) / 2) :
    K * (Q ^ (-κ)) ^ ((2 * (d + 1)) * (2 * (d + 1) - 1) / 2) <
      1 / ((2 * Q) ^ (d * (2 * (d + 1))) * (2 * Q ^ u) ^ (2 * (d + 1))) := by
  have hpos : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  let N := 2 * (d + 1)
  let F : ℝ := 2 ^ (d * N + N)
  have hF : 0 < F := by positivity
  have hKF : K * F < Q :=
    (mul_le_mul_of_nonneg_left (degree_denominator_factor_le hd) hK).trans_lt hthreshold
  have hs := strict_power_comparison hQ (mul_nonneg hK hF.le) hKF hgap
  rw [two_height_denominator_eq hpos]
  have hp : (Q ^ (-κ)) ^ (N * (N - 1) / 2) =
      Q ^ (-(κ * (N : ℝ) * (N - 1) / 2)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le, triangular_natCast]
    congr 1
    ring
  change K * (Q ^ (-κ)) ^ (N * (N - 1) / 2) <
    1 / (F * Q ^ (((d : ℝ) + u) * N))
  rw [hp]
  apply (lt_div_iff₀ (mul_pos hF (Real.rpow_pos_of_pos hpos _))).mpr
  have hs' : K * F * Q ^ (-(κ * (N : ℝ) * (N - 1) / 2)) <
      1 / Q ^ (((d : ℝ) + u) * N) := by
    simpa only [N, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] using hs
  have ht := (lt_div_iff₀ (Real.rpow_pos_of_pos hpos (((d : ℝ) + u) * N))).mp hs'
  convert ht using 1; ring

end MahlerLean
