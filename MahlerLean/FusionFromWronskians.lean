import MahlerLean.WronskianLocalization
import MahlerLean.FusionFromCounting

/-!
The analytic zero sets used by fusion are constructed here. The analytic
Wronskian criterion and Proposition 5.1 remain explicit inputs. No claim
of unconditional escape for nonrational analytic functions is made.
-/

noncomputable section
namespace MahlerLean
open Set

/-- The exact finite degree cutoff D(A) from the manuscript. -/
def wronskianDegreeCutoff (A : ℕ) : ℕ := max 2 ⌈(10 : ℝ) * A / 97⌉₊

theorem wronskianDegreeCutoff_monotone : Monotone wronskianDegreeCutoff := by
  intro A B hAB
  apply max_le_max le_rfl
  apply Nat.ceil_mono
  have h : (A : ℝ) ≤ B := by exact_mod_cast hAB
  linarith

/-- Analytic/counting inputs with no arbitrary forbidden-set sequence.
The two missing mathematical implications are exposed in `wronskian_nonzero`
and `counting`; they are hypotheses, never axioms. -/
structure WronskianCountingInputs (f : ℝ → ℝ) where
  domain : Set ℝ
  domain_preconnected : IsPreconnected domain
  analytic : AnalyticOnNhd ℝ f domain
  left : ℝ
  right : ℝ
  nondegenerate : left < right
  interval_subset : Icc left right ⊆ domain
  M : ℝ
  Clow : ℝ
  M_nonneg : 0 ≤ M
  Clow_nonneg : 0 ≤ Clow
  deriv_bound : ∀ x ∈ Icc left right, |deriv f x| ≤ M
  wronskian_nonzero : ∀ d : ℕ, 2 ≤ d → ∃ y ∈ domain, rationalWronskian f d y ≠ 0
  counting : ∀ n : ℕ, ∀ l u : ℝ, l < u → Icc l u ⊆ Icc left right →
    (∀ d ∈ Finset.Icc 2 (wronskianDegreeCutoff (n + 3)),
      ∀ x ∈ Icc l u, rationalWronskian f d x ≠ 0) →
    ∃ C : ℝ, HasUniformDangerBound f l u M Clow C (n + 3)

/-- The exact union of Wronskian zeros in I_* for 2 <= d <= D(n+3). -/
def WronskianCountingInputs.zeroSet {f : ℝ → ℝ} (e : WronskianCountingInputs f)
    (n : ℕ) : Finset ℝ :=
  Classical.choose (exists_rationalWronskian_zero_finset e.analytic e.domain_preconnected
    (Finset.Icc 2 (wronskianDegreeCutoff (n + 3)))
    (fun d hd => e.wronskian_nonzero d (Finset.mem_Icc.mp hd).1)
    isCompact_Icc e.interval_subset)

theorem mem_wronskian_zeroSet {f : ℝ → ℝ} (e : WronskianCountingInputs f)
    (n : ℕ) (x : ℝ) :
    x ∈ e.zeroSet n ↔ x ∈ Icc e.left e.right ∧
      ∃ d ∈ Finset.Icc 2 (wronskianDegreeCutoff (n + 3)), rationalWronskian f d x = 0 :=
  Classical.choose_spec (exists_rationalWronskian_zero_finset e.analytic e.domain_preconnected
    (Finset.Icc 2 (wronskianDegreeCutoff (n + 3)))
    (fun d hd => e.wronskian_nonzero d (Finset.mem_Icc.mp hd).1)
    isCompact_Icc e.interval_subset) x

theorem wronskian_zeroSet_mono {f : ℝ → ℝ} (e : WronskianCountingInputs f)
    {n m : ℕ} (hnm : n ≤ m) : e.zeroSet n ⊆ e.zeroSet m := by
  intro x hx
  obtain ⟨hxI, d, hd, hz⟩ := (mem_wronskian_zeroSet e n x).mp hx
  apply (mem_wronskian_zeroSet e m x).mpr
  refine ⟨hxI, d, Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1, ?_⟩, hz⟩
  exact (Finset.mem_Icc.mp hd).2.trans
    (wronskianDegreeCutoff_monotone (Nat.add_le_add_right hnm 3))

/-- Insert the analytic finite zero sets and differentiability into fusion. -/
def WronskianCountingInputs.toUniformCountingInputs {f : ℝ → ℝ}
    (e : WronskianCountingInputs f) : UniformCountingInputs f where
  left := e.left
  right := e.right
  nondegenerate := e.nondegenerate
  M := e.M
  Clow := e.Clow
  M_nonneg := e.M_nonneg
  Clow_nonneg := e.Clow_nonneg
  differentiable := fun x hx => (e.analytic x (e.interval_subset hx)).differentiableAt
  deriv_bound := e.deriv_bound
  zeros := e.zeroSet
  counting := by
    intro n l u hlu hsub havoid
    apply e.counting n l u hlu hsub
    intro d hd x hx hz
    exact havoid x hx ((mem_wronskian_zeroSet e n x).mpr ⟨hsub hx, d, hd, hz⟩)

/-- Conditional escape with the manuscript's Wronskian zero sets now
constructed from analyticity and the stated Wronskian nontriviality. -/
theorem exists_escape_of_wronskian_counting {f : ℝ → ℝ} (e : WronskianCountingInputs f) :
    ∃ x : ℝ, ∃ B : ℕ, x ∈ Ioo e.left e.right ∧ 2 ≤ B ∧
      Liouville x ∧ PaperLiouville x ∧
      EventualTargetAvoidance (f x) 100 B ∧ ¬ Liouville (f x) :=
  exists_escape_of_uniform_counting e.toUniformCountingInputs

end MahlerLean
