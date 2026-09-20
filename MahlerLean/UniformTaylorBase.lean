import MahlerLean.CurveTaylorBounds
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

open Set
noncomputable section
namespace MahlerLean

/-- Restricting the interval does not change derivatives on a nondegenerate
subinterval. This allows all constants to be chosen on the parent interval. -/
theorem iteratedDerivWithin_right_subinterval
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Φ : ℝ → E} {a b c x : ℝ} {n : ℕ}
    (hac : a ≤ c) (hcb : c < b)
    (hΦ : ContDiffOn ℝ n Φ (Icc a b)) (hx : x ∈ Icc c b) :
    iteratedDerivWithin n Φ (Icc c b) x = iteratedDerivWithin n Φ (Icc a b) x := by
  unfold iteratedDerivWithin
  rw [iteratedFDerivWithin_subset (Icc_subset_Icc hac le_rfl)
    (uniqueDiffOn_Icc hcb) (uniqueDiffOn_Icc (hac.trans_lt hcb)) hΦ hx]

/-- A derivative bound on the parent compact interval works for every
nondegenerate right subinterval, with one constant chosen beforehand. -/
theorem exists_uniform_derivative_bound_right_subinterval
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Φ : ℝ → E} {a b : ℝ} (hab : a < b) (n : ℕ)
    (hΦ : ContDiffOn ℝ n Φ (Icc a b)) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ c, a ≤ c → c < b → ∀ x ∈ Icc c b,
      ‖iteratedDerivWithin n Φ (Icc c b) x‖ ≤ L := by
  have hc := hΦ.continuousOn_iteratedDerivWithin le_rfl (uniqueDiffOn_Icc hab)
  obtain ⟨L, hL⟩ := bddAbove_def.mp (isCompact_Icc.bddAbove_image hc.norm)
  refine ⟨max L 0, le_max_right _ _, ?_⟩
  intro c hac hcb x hx
  rw [iteratedDerivWithin_right_subinterval hac hcb hΦ hx]
  exact (hL _ ⟨x, ⟨hac.trans hx.1, hx.2⟩, rfl⟩).trans (le_max_left _ _)

/-- Uniform Taylor remainder as the left endpoint moves through a compact
parent interval. The constant is independent of c, rho and x. -/
theorem exists_uniform_taylor_remainder_moving_base
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Φ : ℝ → E} {a b : ℝ} (hab : a < b) (n : ℕ)
    (hΦ : ContDiffOn ℝ (n + 1) Φ (Icc a b)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c, a ≤ c → c < b → ∀ ρ, 0 ≤ ρ →
      ∀ x ∈ Icc c b, x - c ≤ ρ →
      ‖Φ x - taylorWithinEval Φ n (Icc c b) c x‖ ≤ C * ρ ^ (n + 1) := by
  obtain ⟨C, hC, hder⟩ := exists_uniform_derivative_bound_right_subinterval hab (n + 1) hΦ
  refine ⟨C, hC, ?_⟩
  intro c hac hcb ρ hρ x hx hxρ
  have hb := taylor_mean_remainder_bound hcb.le
    (hΦ.mono (Icc_subset_Icc hac le_rfl)) hx (hder c hac hcb)
  have hfac : (1 : ℝ) ≤ n.factorial := by exact_mod_cast Nat.factorial_pos n
  calc
    _ ≤ C * (x - c) ^ (n + 1) / n.factorial := hb
    _ ≤ C * (x - c) ^ (n + 1) :=
      div_le_self (mul_nonneg hC (pow_nonneg (sub_nonneg.mpr hx.1) _)) hfac
    _ ≤ C * ρ ^ (n + 1) := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (sub_nonneg.mpr hx.1) hxρ _) hC

end MahlerLean
