import MahlerLean.CurveTaylorBounds
import MahlerLean.WronskianLocalization
import MahlerLean.TargetLinearDeterminant
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Lean.Elab.Tactic.Omega

/-!
The target-linear analytic curve and its uniform Taylor remainder.
-/

open Set

noncomputable section
namespace MahlerLean

/-- The curve `x ↦ (1,f(x),x,xf(x),...,x^d,x^d f(x))`. -/
def targetLinearCurve (f : ℝ → ℝ) (d : ℕ) (x : ℝ) :
    Fin (2 * (d + 1)) → ℝ :=
  fun j => rationalFamily f d j x

@[simp]
theorem targetLinearCurve_apply (f : ℝ → ℝ) (d : ℕ) (x : ℝ)
    (j : Fin (2 * (d + 1))) :
    targetLinearCurve f d x j = x ^ (j.val / 2) * f x ^ (j.val % 2) := by
  rfl

/-- Rows of the target-linear evaluation matrix lying on the graph are
exactly values of `targetLinearCurve`. -/
theorem targetLinearMatrix_row_eq_curve (f : ℝ → ℝ) (d : ℕ)
    (x : Fin (2 * (d + 1)) → ℝ) (k : Fin (2 * (d + 1))) :
    targetLinearMatrix d x (fun i => f (x i)) k =
      targetLinearCurve f d (x k) := by
  funext j
  rfl

/-- Analyticity of `f` supplies arbitrary finite smoothness of the whole
target-linear curve on every smaller set. -/
theorem targetLinearCurve_contDiffOn
    {f : ℝ → ℝ} {U K : Set ℝ} (hf : AnalyticOnNhd ℝ f U)
    (hKU : K ⊆ U) (d : ℕ) (n : WithTop ℕ∞) :
    ContDiffOn ℝ n (targetLinearCurve f d) K := by
  rw [contDiffOn_pi]
  intro j
  exact ((rationalFamily_analytic hf d j).mono hKU).contDiffOn_of_completeSpace

/-- Uniform order-`N` Taylor remainder for the actual target-linear curve,
where `N = 2(d+1)` is the determinant dimension. -/
theorem exists_targetLinearCurve_taylor_remainder_bound
    {f : ℝ → ℝ} {U : Set ℝ} (hf : AnalyticOnNhd ℝ f U)
    (d : ℕ) {a b : ℝ} (hab : a ≤ b) (hI : Icc a b ⊆ U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ : ℝ), 0 ≤ ρ → ∀ x ∈ Icc a b,
      x - a ≤ ρ →
      ‖targetLinearCurve f d x -
          taylorWithinEval (targetLinearCurve f d) (2 * (d + 1) - 1)
            (Icc a b) a x‖ ≤
        C * ρ ^ (2 * (d + 1)) := by
  apply exists_curve_taylor_remainder_bound
  · omega
  · exact hab
  · exact targetLinearCurve_contDiffOn hf hI d (2 * (d + 1))

end MahlerLean
