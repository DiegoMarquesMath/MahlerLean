import MahlerLean.FusionFromTwoHeight
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
namespace MahlerLean
open Set

/-- Nonconstancy supplies a nonzero derivative somewhere in the connected domain. -/
theorem exists_deriv_ne_zero_of_analytic_nonconstant
    {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (hconn : IsPreconnected U)
    (hf : AnalyticOnNhd ℝ f U)
    (hnc : ∃ x ∈ U, ∃ y ∈ U, f x ≠ f y) :
    ∃ x ∈ U, deriv f x ≠ 0 := by
  by_contra h
  push_neg at h
  obtain ⟨x, hx, y, hy, hxy⟩ := hnc
  exact hxy (hU.is_const_of_deriv_eq_zero hconn
    (fun z hz ↦ (hf z hz).differentiableAt.differentiableWithinAt) h hx hy)

/-- Every compact test interval contains a smaller interval with both derivative bounds. -/
theorem exists_analytic_derivative_interval
    {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (hconn : IsPreconnected U)
    (hf : AnalyticOnNhd ℝ f U)
    (hnc : ∃ x ∈ U, ∃ y ∈ U, f x ≠ f y)
    (a b : ℝ) (hab : a < b) (hI : Icc a b ⊆ U) :
    ∃ l u m M : ℝ, a < l ∧ l < u ∧ u < b ∧ 0 < m ∧ 0 ≤ M ∧
      (∀ x ∈ Icc l u, m ≤ |deriv f x|) ∧
      (∀ x ∈ Icc l u, |deriv f x| ≤ M) := by
  have hd := exists_deriv_ne_zero_of_analytic_nonconstant hU hconn hf hnc
  obtain ⟨l, u, m, hal, hlu, hub, hm, hlower⟩ :=
    exists_interval_analytic_family_separated (Finset.univ : Finset Unit)
      (fun _ ↦ deriv f) hconn (fun _ _ ↦ hf.deriv) (fun _ _ ↦ hd) a b hab hI
  have hsub : Icc l u ⊆ U := fun x hx ↦
    hI ⟨hal.le.trans hx.1, hx.2.trans hub.le⟩
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hf.deriv.continuousOn.mono hsub)
  refine ⟨l, u, m, max 0 M, hal, hlu, hub, hm, le_max_left _ _, ?_, ?_⟩
  · exact fun x hx ↦ hlower () (Finset.mem_univ _) x hx
  · intro x hx
    exact (show |deriv f x| ≤ M by simpa only [Real.norm_eq_abs] using hM x hx).trans
      (le_max_right 0 M)

/-- Local escape without supplied derivative bounds or counting estimates. -/
theorem exists_escape_of_nonconstant_analytic_wronskians
    {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (hconn : IsPreconnected U)
    (hf : AnalyticOnNhd ℝ f U)
    (hnc : ∃ x ∈ U, ∃ y ∈ U, f x ≠ f y)
    (hW : ∀ d : ℕ, 2 ≤ d → ∃ y ∈ U, rationalWronskian f d y ≠ 0)
    (a b : ℝ) (hab : a < b) (hI : Icc a b ⊆ U) :
    ∃ x : ℝ, ∃ B : ℕ, x ∈ Ioo a b ∧ 2 ≤ B ∧
      Liouville x ∧ PaperLiouville x ∧
      EventualTargetAvoidance (f x) 100 B ∧ ¬ Liouville (f x) := by
  obtain ⟨l, u, m, M, hal, hlu, hub, hm, hM, hdm, hdM⟩ :=
    exists_analytic_derivative_interval hU hconn hf hnc a b hab hI
  obtain ⟨x, B, hx, hB, hL, hP, havoid, hnL⟩ :=
    exists_escape_of_analytic_wronskians hU hconn hf hlu
      (fun z hz ↦ hI ⟨hal.le.trans hz.1, hz.2.trans hub.le⟩) hM hm hdm hdM hW
  exact ⟨x, B, ⟨hal.trans hx.1, hx.2.trans hub⟩, hB, hL, hP, havoid, hnL⟩

/-- Escape in every nonempty open subset; only Wronskian nontriviality remains. -/
theorem exists_escape_in_open_of_analytic_wronskians
    {f : ℝ → ℝ} {U V : Set ℝ} (hU : IsOpen U) (hconn : IsPreconnected U)
    (hf : AnalyticOnNhd ℝ f U)
    (hnc : ∃ x ∈ U, ∃ y ∈ U, f x ≠ f y)
    (hW : ∀ d : ℕ, 2 ≤ d → ∃ y ∈ U, rationalWronskian f d y ≠ 0)
    (hV : IsOpen V) (hne : V.Nonempty) (hVU : V ⊆ U) :
    ∃ x : ℝ, ∃ B : ℕ, x ∈ V ∧ 2 ≤ B ∧
      Liouville x ∧ PaperLiouville x ∧
      EventualTargetAvoidance (f x) 100 B ∧ ¬ Liouville (f x) := by
  obtain ⟨c, d, hcd, hcdV⟩ := hV.exists_Ioo_subset hne
  obtain ⟨a, hca, had⟩ := exists_between hcd
  obtain ⟨b, hab, hbd⟩ := exists_between had
  have hI : Icc a b ⊆ V := fun x hx ↦
    hcdV ⟨hca.trans_le hx.1, hx.2.trans_lt hbd⟩
  obtain ⟨x, B, hx, hB, hL, hP, havoid, hnL⟩ :=
    exists_escape_of_nonconstant_analytic_wronskians hU hconn hf hnc hW
      a b hab (hI.trans hVU)
  exact ⟨x, B, hI ⟨hx.1.le, hx.2.le⟩, hB, hL, hP, havoid, hnL⟩

end MahlerLean
