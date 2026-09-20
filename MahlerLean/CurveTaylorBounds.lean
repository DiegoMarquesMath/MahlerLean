import Mathlib.Analysis.Calculus.Taylor

/-!
Taylor remainder bounds for vector-valued curves.  This is the analytic
input used before expanding the target-linear determinant row by row.
-/

open scoped BigOperators Nat
open Set

noncomputable section
namespace MahlerLean

/-- Taylor's theorem on a compact interval, with a nonnegative uniform
constant.  The nonnegativity is recorded because it is needed when the
interval length is enlarged to an external radius. -/
theorem exists_taylor_remainder_bound_nonneg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Φ : ℝ → E} {a b : ℝ} {n : ℕ} (hab : a ≤ b)
    (hΦ : ContDiffOn ℝ (n + 1) Φ (Icc a b)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc a b,
      ‖Φ x - taylorWithinEval Φ n (Icc a b) a x‖ ≤
        C * (x - a) ^ (n + 1) := by
  obtain ⟨C, hC⟩ := exists_taylor_mean_remainder_bound hab hΦ
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro x hx
  refine (hC x hx).trans ?_
  exact mul_le_mul_of_nonneg_right (le_max_left C 0)
    (pow_nonneg (sub_nonneg.mpr hx.1) _)

/-- If `x` is at distance at most `ρ` from the left endpoint, the Taylor
remainder is bounded by the same constant times `ρ^(n+1)`. -/
theorem taylor_remainder_le_radius
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Φ : ℝ → E} {a b C ρ x : ℝ} {n : ℕ}
    (hC0 : 0 ≤ C)
    (hrem : ‖Φ x - taylorWithinEval Φ n (Icc a b) a x‖ ≤
      C * (x - a) ^ (n + 1))
    (hxa : 0 ≤ x - a) (hxρ : x - a ≤ ρ) :
    ‖Φ x - taylorWithinEval Φ n (Icc a b) a x‖ ≤ C * ρ ^ (n + 1) := by
  refine hrem.trans ?_
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hxa hxρ _) hC0

/-- Uniform vector Taylor control on every subradius of a compact interval. -/
theorem exists_taylor_remainder_bound_on_radius
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Φ : ℝ → E} {a b : ℝ} {n : ℕ} (hab : a ≤ b)
    (hΦ : ContDiffOn ℝ (n + 1) Φ (Icc a b)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ : ℝ), 0 ≤ ρ → ∀ x ∈ Icc a b,
      x - a ≤ ρ →
      ‖Φ x - taylorWithinEval Φ n (Icc a b) a x‖ ≤
        C * ρ ^ (n + 1) := by
  obtain ⟨C, hC0, hC⟩ :=
    exists_taylor_remainder_bound_nonneg hab hΦ
  refine ⟨C, hC0, ?_⟩
  intro ρ _hρ x hx hxρ
  exact taylor_remainder_le_radius hC0 (hC x hx)
    (sub_nonneg.mpr hx.1) hxρ

/-- The form used for an `N`-dimensional determinant: Taylor order
`N - 1` and remainder of order `N`. -/
theorem exists_curve_taylor_remainder_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Φ : ℝ → E} {a b : ℝ} {N : ℕ} (hN : 0 < N) (hab : a ≤ b)
    (hΦ : ContDiffOn ℝ N Φ (Icc a b)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ : ℝ), 0 ≤ ρ → ∀ x ∈ Icc a b,
      x - a ≤ ρ →
      ‖Φ x - taylorWithinEval Φ (N - 1) (Icc a b) a x‖ ≤
        C * ρ ^ N := by
  have horder : N - 1 + 1 = N := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hN.ne')
  have hΦ' : ContDiffOn ℝ ((N - 1 + 1 : ℕ) : WithTop ℕ∞) Φ (Icc a b) := by
    simpa [horder] using hΦ
  simpa [horder] using
    (exists_taylor_remainder_bound_on_radius
      (Φ := Φ) (a := a) (b := b) (n := N - 1) hab hΦ')

/-- The explicit finite-sum form of the vector Taylor polynomial used in
the determinant expansion. -/
theorem taylorWithinEval_eq_derivative_sum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Φ : ℝ → E) (n : ℕ) (s : Set ℝ) (a x : ℝ) :
    taylorWithinEval Φ n s a x =
      ∑ k ∈ Finset.range (n + 1),
        (((k ! : ℝ)⁻¹ * (x - a) ^ k) •
          iteratedDerivWithin k Φ s a) := by
  exact taylor_within_apply Φ n s a x

end MahlerLean
