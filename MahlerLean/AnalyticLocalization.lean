import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Topology.Order.Compact
import MahlerLean.FiniteAvoidance

/-!
Compact localization for real-analytic functions. Nontriviality is an
explicit hypothesis: this file does not prove the analytic Wronskian
criterion or deduce it from nonrationality of the manuscript's function.
-/

namespace MahlerLean

open Set Filter
open scoped Topology

/-- A nontrivial analytic function on a preconnected domain has finitely
many zeros in any compact subset of that domain. -/
theorem analytic_zeros_finite_on_compact
    {g : ℝ → ℝ} {U K : Set ℝ}
    (hg : AnalyticOnNhd ℝ g U) (hU : IsPreconnected U)
    (hnonzero : ∃ y ∈ U, g y ≠ 0)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    {x ∈ K | g x = 0}.Finite := by
  by_contra hinfinite
  obtain ⟨x, hxK, hacc⟩ :=
    (show {x ∈ K | g x = 0}.Infinite from hinfinite).exists_accPt_of_subset_isCompact
      hK (show {x ∈ K | g x = 0} ⊆ K from fun _ h => h.1)
  have hfreq : ∃ᶠ z in 𝓝[≠] x, g z = 0 :=
    (frequently_mem_iff_neBot.mpr hacc).mono fun _ h => h.2
  have hzero := hg.eqOn_zero_of_preconnected_of_frequently_eq_zero hU (hKU hxK) hfreq
  obtain ⟨y, hy, hny⟩ := hnonzero
  exact hny (hzero hy)

/-- All zeros from a finite family on a compact set can be put in a
single finite forbidden set, with an exact membership specification. -/
theorem exists_analytic_zero_finset
    {ι : Type*} (D : Finset ι) (g : ι → ℝ → ℝ) {U K : Set ℝ}
    (hU : IsPreconnected U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hg : ∀ i ∈ D, AnalyticOnNhd ℝ (g i) U)
    (hnonzero : ∀ i ∈ D, ∃ y ∈ U, g i y ≠ 0) :
    ∃ Z : Finset ℝ, ∀ x, x ∈ Z ↔ x ∈ K ∧ ∃ i ∈ D, g i x = 0 := by
  classical
  have hfin : (⋃ i ∈ D, {x ∈ K | g i x = 0}).Finite :=
    D.finite_toSet.biUnion fun i hi =>
      analytic_zeros_finite_on_compact (hg i hi) hU (hnonzero i hi) hK hKU
  refine ⟨hfin.toFinset, ?_⟩
  intro x
  simp only [Set.Finite.mem_toFinset, Set.mem_iUnion, Set.mem_setOf_eq]
  constructor
  · rintro ⟨i, hi, hx, hz⟩
    exact ⟨hx, i, hi, hz⟩
  · rintro ⟨hx, i, hi, hz⟩
    exact ⟨i, hi, hx, hz⟩

/-- Compactness turns pointwise nonvanishing into a positive lower bound. -/
theorem exists_pos_abs_lower_bound
    {g : ℝ → ℝ} {K : Set ℝ} (hK : IsCompact K)
    (hg : ContinuousOn g K) (hzero : ∀ x ∈ K, g x ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, δ ≤ |g x| := by
  by_cases hne : K.Nonempty
  · obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hne hg.abs
    exact ⟨|g x|, abs_pos.mpr (hzero x hx), fun y hy => hmin hy⟩
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x hx
    exact (hne ⟨x, hx⟩).elim

/-- One positive constant works for every member of a finite family. -/
theorem exists_uniform_pos_abs_lower_bound
    {ι : Type*} (D : Finset ι) (g : ι → ℝ → ℝ) {K : Set ℝ}
    (hK : IsCompact K) (hg : ∀ i ∈ D, ContinuousOn (g i) K)
    (hzero : ∀ i ∈ D, ∀ x ∈ K, g i x ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i ∈ D, ∀ x ∈ K, δ ≤ |g i x| := by
  classical
  induction D using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert i D hi ih =>
    obtain ⟨δ₁, hδ₁, hbound₁⟩ := exists_pos_abs_lower_bound hK
      (hg i (Finset.mem_insert_self _ _)) (hzero i (Finset.mem_insert_self _ _))
    obtain ⟨δ₂, hδ₂, hbound₂⟩ := ih
      (fun j hj => hg j (Finset.mem_insert_of_mem hj))
      (fun j hj => hzero j (Finset.mem_insert_of_mem hj))
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
    intro j hj x hx
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact (min_le_left _ _).trans (hbound₁ x hx)
    · exact (min_le_right _ _).trans (hbound₂ j hj x hx)

/-- Inside any nondegenerate compact interval, finitely many nontrivial
analytic functions are simultaneously separated from zero on a smaller
nondegenerate compact interval. -/
theorem exists_interval_analytic_family_separated
    {ι : Type*} (D : Finset ι) (g : ι → ℝ → ℝ) {U : Set ℝ}
    (hU : IsPreconnected U)
    (hg : ∀ i ∈ D, AnalyticOnNhd ℝ (g i) U)
    (hnonzero : ∀ i ∈ D, ∃ y ∈ U, g i y ≠ 0)
    (a b : ℝ) (hab : a < b) (hI : Icc a b ⊆ U) :
    ∃ l u δ : ℝ, a < l ∧ l < u ∧ u < b ∧ 0 < δ ∧
      ∀ i ∈ D, ∀ x ∈ Icc l u, δ ≤ |g i x| := by
  obtain ⟨Z, hZ⟩ := exists_analytic_zero_finset D g hU isCompact_Icc hI hg hnonzero
  obtain ⟨l, u, hal, hlu, hub, _, havoid⟩ :=
    exists_interval_avoiding_finset Z a b (Z.card + 1) hab (Nat.lt_succ_self _)
  have hsub : Icc l u ⊆ Icc a b := fun x hx => ⟨hal.le.trans hx.1, hx.2.trans hub.le⟩
  obtain ⟨δ, hδ, hbound⟩ := exists_uniform_pos_abs_lower_bound D g isCompact_Icc
    (fun i hi => (hg i hi).continuousOn.mono (hsub.trans hI))
    (by
      intro i hi x hx hz
      exact havoid x hx ((hZ x).mpr ⟨hsub hx, i, hi, hz⟩))
  exact ⟨l, u, δ, hal, hlu, hub, hδ, hbound⟩

end MahlerLean
