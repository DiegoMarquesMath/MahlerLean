import MahlerLean.UniformIntervalCover
import MahlerLean.SublevelIntervals
import MahlerLean.LocalUniformSublevel

/-!
Uniform pairwise-disjoint interval covers for analytic sublevels.  The earlier
compactness construction provides finitely many local derivative patches.  We
collect all local boundary points and cut the global interval only once; this
produces the disjoint component format required by Farey counting.
-/

open Set
open scoped BigOperators

noncomputable section
namespace MahlerLean

/-- Uniform interval complexity with pairwise-disjoint pieces. -/
theorem exists_uniform_analytic_sublevel_disjoint_interval_cover
    {N : ℕ} (hN : 0 < N) (φ : Fin N → ℝ → ℝ)
    {U : Set ℝ} (hU : IsOpen U) (hφ : ∀ j, AnalyticOnNhd ℝ (φ j) U)
    {A B : ℝ} (hJU : Icc A B ⊆ U)
    (hW : ∀ x ∈ Icc A B, wronskian φ x ≠ 0) :
    ∃ lam : ℝ, 0 < lam ∧ ∃ R : ℕ,
      ∀ c : EuclideanSpace ℝ (Fin N), ‖c‖ = 1 →
      ∀ eps : ℝ, eps < lam →
      ∃ t : Finset (Set ℝ), t.card ≤ R ∧
        (∀ E ∈ t, E.OrdConnected) ∧
        (t : Set (Set ℝ)).PairwiseDisjoint id ∧
        (∀ x, (x ∈ Icc A B ∧ ‖jetLinearCombo φ c x‖ ≤ eps) ↔
          ∃ E ∈ t, x ∈ E) := by
  classical
  obtain ⟨eta, heta, k, C, a, b, _hC, _hcenter, hIU, hbound, t, hcover⟩ :=
    exists_finite_uniform_jet_interval_cover_of_analytic
      hN φ hU hφ isCompact_Icc hJU hW
  refine ⟨eta / 2, by linarith, 4 * t.card * (N - 1) + 1, ?_⟩
  intro c hc eps heps
  let s := t.filter (fun p ↦ c ∈ C p)
  have hlocal : ∀ p : {p // p ∈ s},
      ∃ D : Finset ℝ, D.card ≤ 2 * (N - 1) ∧
        ∀ x ∈ Icc (a p.val) (b p.val),
          ‖jetLinearCombo φ c x‖ = eps → x ∈ D := by
    intro p
    have hcp : c ∈ C p.val := (Finset.mem_filter.mp p.property).2
    have hlow : ∀ x ∈ Icc (a p.val) (b p.val),
        eta / 2 ≤ |jetApply φ c (k p.val) x| :=
      hbound p.val c hcp
    by_cases hk : (k p.val).val = 0
    · refine ⟨∅, by simp, ?_⟩
      intro x hxI hxeq
      have hempty := jetLinearCombo_sublevel_eq_empty_of_zero_order
        φ c hφ (k p.val) hk (hIU p.val) heps hlow
      have hxmem : x ∈
          {z | z ∈ Icc (a p.val) (b p.val) ∧
            ‖jetLinearCombo φ c z‖ ≤ eps} := ⟨hxI, hxeq.le⟩
      rw [hempty] at hxmem
      exact hxmem.elim
    · obtain ⟨hcont, _⟩ :=
        analyticFamily_linearCombo_smooth φ c hφ (hIU p.val)
      have hder : ∀ x ∈ Icc (a p.val) (b p.val),
          eta / 2 ≤
            |iteratedDeriv (k p.val).val (jetLinearCombo φ c) x| := by
        intro x hx
        rw [iteratedDeriv_jetLinearCombo_eq_jetApply
          φ c hφ (hIU p.val hx) (k p.val)]
        exact hlow x hx
      let Z : Set ℝ :=
        {x | x ∈ Icc (a p.val) (b p.val) ∧
          |jetLinearCombo φ c x| = eps}
      have hZ := abs_boundary_set_finite_and_ncard_le
          (g := jetLinearCombo φ c) (k := (k p.val).val)
          (a := a p.val) (b := b p.val) (eps := eps) (lam := eta / 2)
          (Nat.pos_of_ne_zero hk) hcont (by linarith) hder
      change Z.Finite ∧ Z.ncard ≤ 2 * (k p.val).val at hZ
      obtain ⟨hZfin, hZcard⟩ := hZ
      refine ⟨hZfin.toFinset, ?_, ?_⟩
      · rw [← Set.ncard_eq_toFinset_card Z hZfin]
        have hklt := (k p.val).isLt
        omega
      · intro x hxI hxeq
        exact hZfin.mem_toFinset.mpr ⟨hxI, by simpa [Real.norm_eq_abs] using hxeq⟩
  choose D hDcard hDcov using hlocal
  let allBoundary : Finset ℝ := Finset.univ.biUnion D
  have hBoundaryCard : allBoundary.card ≤ s.card * (2 * (N - 1)) := by
    calc
      allBoundary.card ≤ ∑ p : {p // p ∈ s}, (D p).card := by
        simpa [allBoundary] using
          (Finset.card_biUnion_le (s := Finset.univ) (t := D))
      _ ≤ ∑ _p : {p // p ∈ s}, 2 * (N - 1) :=
        Finset.sum_le_sum (fun p _ ↦ hDcard p)
      _ = s.card * (2 * (N - 1)) := by simp
  have hBoundaryCover : ∀ x ∈ Icc A B,
      ‖jetLinearCombo φ c x‖ = eps → x ∈ allBoundary := by
    intro x hxI hxeq
    have hq : (c, x) ∈ coefficientSourceProduct N (Icc A B) :=
      (mem_coefficientSourceProduct (K := Icc A B) (c, x)).mpr ⟨hc, hxI⟩
    obtain ⟨p, hpt, hcp, hxp⟩ := hcover (c, x) hq
    have hps : p ∈ s := Finset.mem_filter.mpr ⟨hpt, hcp⟩
    have hxD : x ∈ D ⟨p, hps⟩ :=
      hDcov ⟨p, hps⟩ x ⟨hxp.1.le, hxp.2.le⟩ hxeq
    exact Finset.mem_biUnion.mpr ⟨⟨p, hps⟩, Finset.mem_univ _, hxD⟩
  have hgcont : ContinuousOn (jetLinearCombo φ c) (Icc A B) :=
    (analyticOnNhd_jetLinearCombo φ c hφ).continuousOn.mono hJU
  obtain ⟨u, hucard, huconn, hudis, hucov⟩ :=
    sublevel_interval_cover_of_boundary_finset
      ordConnected_Icc hgcont allBoundary hBoundaryCover
  refine ⟨u, ?_, huconn, hudis, hucov⟩
  calc
    u.card ≤ 2 * allBoundary.card + 1 := hucard
    _ ≤ 2 * (s.card * (2 * (N - 1))) + 1 := by omega
    _ = 4 * s.card * (N - 1) + 1 := by ring
    _ ≤ 4 * t.card * (N - 1) + 1 := by
      have hscard : s.card ≤ t.card := Finset.card_filter_le _ _
      exact Nat.add_le_add_right
        (Nat.mul_le_mul_right (N - 1) (Nat.mul_le_mul_left 4 hscard)) 1

end MahlerLean
