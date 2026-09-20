import MahlerLean.WronskianLeadingTerm

/-! Nonrationality discharges the Wronskian hypothesis for the manuscript's
exact rational family. No Wronskian nonvanishing assumption is added. -/
noncomputable section
open Set Filter
open scoped Topology
namespace MahlerLean

/-- At every base point, the rational-family Wronskian is nonzero sufficiently
nearby away from that point. -/
theorem eventually_rationalWronskian_ne_zero_of_not_rational
    {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (hconn : IsPreconnected U)
    (hf : AnalyticOnNhd ℝ f U) (hnr : ¬ IsRationalOn f U)
    (d : ℕ) {z : ℝ} (hz : z ∈ U) :
    ∀ᶠ x in 𝓝[≠] z, rationalWronskian f d x ≠ 0 := by
  obtain ⟨b, r, hr, horders⟩ := rationalFamily_exists_basis_distinct_orders
    hU ⟨z, hz⟩ hconn hf hnr d hz
  have hcombo (i : Fin (2 * (d+1))) :
      AnalyticOnNhd ℝ (fun x ↦ ∑ j, b i j * rationalFamily f d j x) U :=
    Finset.analyticOnNhd_fun_sum _
      (fun j _ ↦ analyticOnNhd_const.mul (rationalFamily_analytic hf d j))
  have hw := eventually_wronskian_ne_zero_of_distinct_orders
    (fun i x ↦ ∑ j, b i j * rationalFamily f d j x) r
    (fun i ↦ hcombo i z hz) hr (fun i ↦ (horders i).1) (fun i ↦ (horders i).2)
  have hmem : ∀ᶠ x in 𝓝[≠] z, x ∈ U :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (hU.mem_nhds hz)
  filter_upwards [hw, hmem] with x hx hxu
  exact (wronskian_basis_ne_zero_iff (rationalFamily f d) b
    (rationalFamily_analytic hf d) hxu).mp hx

/-- Every rational-family Wronskian is nontrivial on the analytic domain. -/
theorem exists_rationalWronskian_ne_zero_of_not_rational
    {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (hne : U.Nonempty)
    (hconn : IsPreconnected U) (hf : AnalyticOnNhd ℝ f U)
    (hnr : ¬ IsRationalOn f U) (d : ℕ) :
    ∃ x ∈ U, rationalWronskian f d x ≠ 0 := by
  obtain ⟨z, hz⟩ := hne
  have hw := eventually_rationalWronskian_ne_zero_of_not_rational hU hconn hf hnr d hz
  have hmem : ∀ᶠ x in 𝓝[≠] z, x ∈ U :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (hU.mem_nhds hz)
  exact (hmem.and hw).exists

/-- The escape conclusion now follows from analyticity and nonrationality alone;
all Wronskian and derivative hypotheses have been discharged. -/
theorem exists_escape_of_analytic_not_rational
    {f : ℝ → ℝ} {U V : Set ℝ} (hU : IsOpen U) (hconn : IsPreconnected U)
    (hf : AnalyticOnNhd ℝ f U) (hnr : ¬ IsRationalOn f U)
    (hV : IsOpen V) (hne : V.Nonempty) (hVU : V ⊆ U) :
    ∃ x : ℝ, ∃ B : ℕ, x ∈ V ∧ 2 ≤ B ∧
      Liouville x ∧ PaperLiouville x ∧
      EventualTargetAvoidance (f x) 100 B ∧ ¬ Liouville (f x) := by
  apply exists_escape_of_not_rational_and_wronskians hU hconn hf hnr
    (fun d _ ↦ exists_rationalWronskian_ne_zero_of_not_rational
      hU (hne.mono hVU) hconn hf hnr d) hV hne hVU

end MahlerLean
