import MahlerLean.FareySupply
import MahlerLean.FusionEscape

/-!
The analytic/counting interface after proving Lemma 2.2. Rational source
supply is supplied by a theorem, not a field in the input. Proposition 5.1
and the interpretation of the finite forbidden sets as Wronskian zeros
still have to be proved from the manuscript's analytic hypotheses.
-/
namespace MahlerLean
open Set

/-- Inputs still required from the analytic argument. The absolute Farey
constant is fixed at 1/4 and its estimate is no longer an assumption. -/
structure UniformCountingInputs (f : ℝ → ℝ) where
  left : ℝ
  right : ℝ
  nondegenerate : left < right
  M : ℝ
  Clow : ℝ
  M_nonneg : 0 ≤ M
  Clow_nonneg : 0 ≤ Clow
  differentiable : ∀ x ∈ Icc left right, DifferentiableAt ℝ f x
  deriv_bound : ∀ x ∈ Icc left right, |deriv f x| ≤ M
  zeros : ℕ → Finset ℝ
  counting : ∀ n : ℕ, ∀ l u : ℝ, l < u → Icc l u ⊆ Icc left right →
    (∀ x ∈ Icc l u, x ∉ zeros n) →
    ∃ C : ℝ, HasUniformDangerBound f l u M Clow C (n + 3)

/-- Insert the proved rational supply into the existing fusion interface. -/
noncomputable def UniformCountingInputs.toFusionInputs {f : ℝ → ℝ} (d : UniformCountingInputs f) :
    FusionInputs f where
  left := d.left
  right := d.right
  nondegenerate := d.nondegenerate
  M := d.M
  Clow := d.Clow
  cF := 1/4
  M_nonneg := d.M_nonneg
  Clow_nonneg := d.Clow_nonneg
  cF_pos := by norm_num
  differentiable := d.differentiable
  deriv_bound := d.deriv_bound
  zeros := d.zeros
  supply := fun l u hlu _ => sourceFractions_quarter_supply l u hlu
  counting := d.counting

/-- Fusion and escape with rational source supply discharged by Lemma 2.2.
Only the explicit analytic/counting interface remains conditional. -/
theorem exists_escape_of_uniform_counting {f : ℝ → ℝ} (d : UniformCountingInputs f) :
    ∃ x : ℝ, ∃ B : ℕ, x ∈ Ioo d.left d.right ∧ 2 ≤ B ∧
      Liouville x ∧ PaperLiouville x ∧
      EventualTargetAvoidance (f x) 100 B ∧ ¬ Liouville (f x) := by
  exact exists_escape_of_counting d.toFusionInputs

end MahlerLean
