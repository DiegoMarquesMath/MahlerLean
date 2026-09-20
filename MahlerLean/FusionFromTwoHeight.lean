import MahlerLean.TwoHeightCounting

/-! Proposition 5.1 discharges the counting hypothesis of analytic fusion.
Wronskian nontriviality is still an explicit analytic hypothesis. -/
noncomputable section
namespace MahlerLean
open Set

/-- Escape from analytic and Wronskian data, with no counting hypothesis. -/
theorem exists_escape_of_analytic_wronskians
    {f : ℝ → ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hconn : IsPreconnected U)
    (hf : AnalyticOnNhd ℝ f U)
    {a b m M : ℝ} (hab : a < b) (hIU : Icc a b ⊆ U)
    (hM : 0 ≤ M) (hm : 0 < m)
    (hdm : ∀ x ∈ Icc a b, m ≤ |deriv f x|)
    (hdM : ∀ x ∈ Icc a b, |deriv f x| ≤ M)
    (hW : ∀ d : ℕ, 2 ≤ d → ∃ y ∈ U, rationalWronskian f d y ≠ 0) :
    ∃ x : ℝ, ∃ B : ℕ, x ∈ Ioo a b ∧ 2 ≤ B ∧
      Liouville x ∧ PaperLiouville x ∧
      EventualTargetAvoidance (f x) 100 B ∧ ¬ Liouville (f x) := by
  obtain ⟨Clow, hClow, hcount⟩ :=
    proposition_5_1_uniformDangerBound hU hf hIU hM hm hdm
  let e : WronskianCountingInputs f := {
    domain := U
    domain_preconnected := hconn
    analytic := hf
    left := a
    right := b
    nondegenerate := hab
    interval_subset := hIU
    M := M
    Clow := Clow
    M_nonneg := hM
    Clow_nonneg := hClow.le
    deriv_bound := hdM
    wronskian_nonzero := hW
    counting := by
      intro n l u hlu hsub hWr
      obtain ⟨C, _, hC⟩ := hcount l u hlu hsub (n + 3) (by omega)
        (fun d hd hD ↦ hWr d (Finset.mem_Icc.mpr ⟨hd, hD⟩))
      exact ⟨C, hC⟩ }
  exact exists_escape_of_wronskian_counting e

end MahlerLean
