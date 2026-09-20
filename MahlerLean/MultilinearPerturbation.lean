import MahlerLean.DeterminantRowExpansion
import MahlerLean.LargeTargetParameters
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
The multilinear route (4.8)--(4.9). The analytic estimate for each mixed
term remains an explicit hypothesis: no unproved exterior-decay assertion
is hidden in these statements. The scalar corollary and the large-target
threshold are unconditional consequences of the stated inequalities.
-/
open scoped BigOperators
noncomputable section
namespace MahlerLean

/-- Radius exponent contributed by the remaining curve vectors. -/
def mixedCurveExponent (N r : ℕ) : ℝ :=
  ((N : ℝ) - r) * ((N : ℝ) - r - 1) / 2

/-- The exponent identity in (4.9), with natural numbers of rows. -/
theorem mixed_perturbation_exponent_identity (N r : ℕ) :
    (N : ℝ) * r + mixedCurveExponent N r =
      (N : ℝ) * (N - 1) / 2 + (r : ℝ) * (r + 1) / 2 := by
  unfold mixedCurveExponent
  ring

/-- Every mixed summand has at least the triangular decay when delta ≤ rho^N. -/
theorem mixed_perturbation_term_le {N r : ℕ} {ρ δ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hδ : 0 ≤ δ) (hsmall : δ ≤ ρ ^ N) :
    δ ^ r * ρ ^ mixedCurveExponent N r ≤ ρ ^ ((N : ℝ) * (N - 1) / 2) := by
  calc
    δ ^ r * ρ ^ mixedCurveExponent N r ≤
        (ρ ^ N) ^ r * ρ ^ mixedCurveExponent N r :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hδ hsmall r)
        (Real.rpow_nonneg hρ.le _)
    _ = ρ ^ ((N : ℝ) * r + mixedCurveExponent N r) := by
      rw [← pow_mul, ← Real.rpow_natCast, ← Real.rpow_add hρ]
      simp only [Nat.cast_mul]
    _ ≤ ρ ^ ((N : ℝ) * (N - 1) / 2) := by
      apply Real.rpow_le_rpow_of_exponent_ge hρ hρ1
      rw [mixed_perturbation_exponent_identity]
      exact le_add_of_nonneg_right (by positivity)

/-- Scalar corollary of (4.8), including the harmless factor N+1. -/
theorem mixed_perturbation_sum_le {N : ℕ} {ρ δ C : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hδ : 0 ≤ δ)
    (hsmall : δ ≤ ρ ^ N) (hC : 0 ≤ C) :
    C * (∑ r ∈ Finset.range (N + 1), δ ^ r * ρ ^ mixedCurveExponent N r) ≤
      (C * (N + 1)) * ρ ^ ((N : ℝ) * (N - 1) / 2) := by
  calc
    _ ≤ C * (∑ _r ∈ Finset.range (N + 1),
        ρ ^ ((N : ℝ) * (N - 1) / 2)) := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact Finset.sum_le_sum (fun r _ ↦ mixed_perturbation_term_le hρ hρ1 hδ hsmall)
    _ = _ := by simp [mul_assoc]

/-- Assemble the multilinear bound from estimates for all mixed terms.
The factor 2^N avoids grouping by binomial coefficients. -/
theorem abs_det_add_le_mixed_sum {N : ℕ}
    (P E : Matrix (Fin N) (Fin N) ℝ) {C ρ δ : ℝ}
    (hC : 0 ≤ C) (hρ : 0 ≤ ρ) (hδ : 0 ≤ δ)
    (hmixed : ∀ choice : Fin N → Bool,
      |Matrix.det (fun i ↦ if choice i then E i else P i)| ≤
        C * δ ^ (Finset.univ.filter (fun i ↦ choice i = true)).card *
          ρ ^ mixedCurveExponent N (Finset.univ.filter (fun i ↦ choice i = true)).card) :
    |(P + E).det| ≤
      (Fintype.card (Fin N → Bool) * C) *
        (∑ r ∈ Finset.range (N + 1), δ ^ r * ρ ^ mixedCurveExponent N r) := by
  rw [det_add_rows_eq_sum_bool]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    (∑ choice : Fin N → Bool,
        |Matrix.det (fun i ↦ if choice i then E i else P i)|) ≤
      ∑ _choice : Fin N → Bool,
        C * (∑ r ∈ Finset.range (N + 1), δ ^ r * ρ ^ mixedCurveExponent N r) := by
      apply Finset.sum_le_sum
      intro choice _
      let r := (Finset.univ.filter (fun i ↦ choice i = true)).card
      have hr : r < N + 1 := by
        have := Finset.card_filter_le (s := (Finset.univ : Finset (Fin N)))
          (p := fun i ↦ choice i = true)
        simpa [r] using Nat.lt_succ_of_le this
      have ht : δ ^ r * ρ ^ mixedCurveExponent N r ≤
          ∑ k ∈ Finset.range (N + 1), δ ^ k * ρ ^ mixedCurveExponent N k :=
        Finset.single_le_sum (f := fun k ↦ δ ^ k * ρ ^ mixedCurveExponent N k) (fun k _ ↦ mul_nonneg (pow_nonneg hδ _)
          (Real.rpow_nonneg hρ _)) (Finset.mem_range.mpr hr)
      exact (hmixed choice).trans (by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left ht hC)
    _ = _ := by simp [mul_assoc]

/-- Corollary of the multilinear estimate under delta ≤ rho^N.
The mixed-term estimate is still an explicit analytic input. -/
theorem abs_det_add_le_triangular_of_mixed_bounds {N : ℕ}
    (P E : Matrix (Fin N) (Fin N) ℝ) {C ρ δ : ℝ}
    (hC : 0 ≤ C) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hδ : 0 ≤ δ)
    (hsmall : δ ≤ ρ ^ N)
    (hmixed : ∀ choice : Fin N → Bool,
      |Matrix.det (fun i ↦ if choice i then E i else P i)| ≤
        C * δ ^ (Finset.univ.filter (fun i ↦ choice i = true)).card *
          ρ ^ mixedCurveExponent N (Finset.univ.filter (fun i ↦ choice i = true)).card) :
    |(P + E).det| ≤
      ((Fintype.card (Fin N → Bool) * C) * (N + 1)) *
        ρ ^ ((N : ℝ) * (N - 1) / 2) := by
  exact (abs_det_add_le_mixed_sum P E hC hρ.le hδ hmixed).trans
    (mixed_perturbation_sum_le hρ hρ1 hδ hsmall
      (mul_nonneg (Nat.cast_nonneg _) hC))

/-- The exact uniform threshold K0^5 in Proposition 5.1. -/
theorem perturbation_small_of_exponent_gap {Q K s κ : ℝ} {N : ℕ}
    (hQ : 1 ≤ Q) (hK : 0 ≤ K) (hthreshold : K ^ 5 ≤ Q)
    (hgap : (1 : ℝ) / 5 ≤ s - κ * N) :
    K * Q ^ (-s) ≤ (Q ^ (-κ)) ^ N := by
  have hpos : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have hroot : K ≤ Q ^ ((1 : ℝ) / 5) := by
    have h := Real.rpow_le_rpow (pow_nonneg hK 5) hthreshold
      (show (0 : ℝ) ≤ (5 : ℝ)⁻¹ by positivity)
    have heq : (K ^ 5) ^ ((5 : ℝ)⁻¹) = K := by
      simpa using Real.pow_rpow_inv_natCast hK (by decide : (5 : ℕ) ≠ 0)
    rw [heq] at h
    simpa only [one_div] using h
  calc
    K * Q ^ (-s) ≤ Q ^ ((1 : ℝ) / 5) * Q ^ (-s) :=
      mul_le_mul_of_nonneg_right hroot (Real.rpow_nonneg hpos.le _)
    _ = Q ^ ((1 : ℝ) / 5 - s) := by rw [← Real.rpow_add hpos]; rfl
    _ ≤ Q ^ ((-κ) * N) := Real.rpow_le_rpow_of_exponent_le hQ (by linarith)
    _ = (Q ^ (-κ)) ^ N := by
      rw [Real.rpow_mul hpos.le, Real.rpow_natCast]

/-- Specialization to the actual adaptive degree and exponents of large blocks. -/
theorem largeTarget_vertical_error_le_radius_power
    (A : ℕ) (u : ℝ) {Q K : ℝ}
    (hu : (1 : ℝ) / 5 ≤ u) (huA : 97 * u < (A : ℝ))
    (hQ : 1 ≤ Q) (hK : 0 ≤ K) (hthreshold : K ^ 5 ≤ Q) :
    K * Q ^ (-largeTargetS A u) ≤
      (Q ^ (-largeTargetKappa u)) ^ largeTargetN u := by
  apply perturbation_small_of_exponent_gap hQ hK hthreshold
  simpa only [largeTargetN_cast] using
    largeTargetPerturbationGap_one_fifth A u hu huA

end MahlerLean
