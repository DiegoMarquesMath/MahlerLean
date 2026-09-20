import MahlerLean.SmallTargetCounting
import Mathlib.Analysis.Calculus.Deriv.MeanValue

open Set
namespace MahlerLean

/-- The inverse Lipschitz estimate follows from the manuscript's uniform
lower bound on the absolute derivative by the real mean value theorem. -/
theorem inverse_bound_of_abs_deriv_lower {f : ℝ → ℝ} {a b m : ℝ}
    (hd : ∀ x ∈ Icc a b, DifferentiableAt ℝ f x)
    (hm : ∀ x ∈ Icc a b, m ≤ |deriv f x|) :
    ∀ x ∈ Icc a b, ∀ z ∈ Icc a b, m*|x-z| ≤ |f x-f z| := by
  have hordered : ∀ x ∈ Icc a b, ∀ z ∈ Icc a b, x < z →
      m*(z-x) ≤ |f z-f x| := by
    intro x hx z hz hxz
    have hsub : Icc x z ⊆ Icc a b := by
      intro y hy; exact ⟨hx.1.trans hy.1, hy.2.trans hz.2⟩
    obtain ⟨c, hc, heq⟩ := exists_deriv_eq_slope f hxz
      (fun y hy ↦ (hd y (hsub hy)).continuousAt.continuousWithinAt)
      (fun y hy ↦ (hd y (hsub ⟨hy.1.le, hy.2.le⟩)).differentiableWithinAt)
    have hl := hm c (hsub ⟨hc.1.le, hc.2.le⟩)
    rw [heq, abs_div, abs_of_pos (sub_pos.mpr hxz)] at hl
    exact (le_div_iff₀ (sub_pos.mpr hxz)).mp hl
  intro x hx z hz
  rcases lt_trichotomy x z with h | h | h
  · simpa only [abs_sub_comm x z, abs_of_pos (sub_pos.mpr h), abs_sub_comm (f x) (f z)]
      using hordered x hx z hz h
  · simp [h]
  · simpa only [abs_of_pos (sub_pos.mpr h)] using hordered z hz x hx h

/-- Small-height counting from the fixed derivative and image bounds. -/
theorem exists_smallTarget_counting_of_derivative_bounds
    {f : ℝ → ℝ} {a b F M m : ℝ}
    (hF : 0 ≤ F) (hM : 0 ≤ M) (hm : 0 < m)
    (hf : ∀ x ∈ Icc a b, |f x| ≤ F)
    (hd : ∀ x ∈ Icc a b, DifferentiableAt ℝ f x)
    (hdm : ∀ x ∈ Icc a b, m ≤ |deriv f x|) :
    ∃ C_low C_err : ℝ, 0 < C_low ∧ 0 < C_err ∧
      ∀ A Q : ℕ, 3 ≤ A → 0 < Q → ∀ H : ℝ, 1 ≤ H → ∀ S : Finset ℚ,
        (∀ r ∈ S, r.den < 2*Q) →
        (∀ r ∈ S, (r : ℝ) ∈ Icc a b) →
        (∀ r ∈ S, ∃ k : ℕ, (2 : ℝ)^k*H < (Q : ℝ)^((1 : ℝ)/5) ∧
          ∃ p : ℤ, ∃ q : ℕ, 0 < q ∧ (2 : ℝ)^k*H ≤ (q : ℝ) ∧
            (q : ℝ) < 2*((2 : ℝ)^k*H) ∧
            |f r-(p : ℝ)/q| ≤ safetyMargin M Q A q) →
        (S.card : ℝ) ≤ C_low*(Q : ℝ)^2*(H^98)⁻¹ + C_err*(Q : ℝ)^((2 : ℝ)/5) :=
  exists_smallTarget_original_margin_card_bound hF hM hm hf
    (inverse_bound_of_abs_deriv_lower hd hdm)

end MahlerLean
