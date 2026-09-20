import MahlerLean.SublevelOneDim

open Set
open scoped Interval

noncomputable section
namespace MahlerLean

/-- On an interval with no hits of the boundary level, a continuous
sublevel is itself an interval (possibly empty). -/
theorem sublevel_ordConnected_of_no_level
    {S : Set ℝ} {g : ℝ → ℝ} {eps : ℝ}
    (hS : S.OrdConnected) (hg : ContinuousOn g S)
    (hno : ∀ x ∈ S, ‖g x‖ ≠ eps) :
    {x | x ∈ S ∧ ‖g x‖ ≤ eps}.OrdConnected := by
  constructor
  intro x hx y hy z hz
  have hzS : z ∈ S := hS.out hx.1 hy.1 hz
  refine ⟨hzS, ?_⟩
  by_contra hn
  have hgt : eps < ‖g z‖ := lt_of_not_ge hn
  have hlt : ‖g x‖ < eps := lt_of_le_of_ne hx.2 (hno x hx.1)
  have hseg : [[x,z]] ⊆ S := hS.uIcc_subset hx.1 hzS
  have he : eps ∈ [[‖g x‖, ‖g z‖]] := by
    rw [uIcc_of_le (hlt.le.trans hgt.le)]
    exact ⟨hlt.le, hgt.le⟩
  obtain ⟨w, hw, heq⟩ := intermediate_value_uIcc (hg.norm.mono hseg) he
  exact hno w (hseg hw) heq

/-- Cutting at a finite set containing every boundary-level hit gives
at most `2 * B.card + 1` interval pieces. Singleton pieces are retained,
so the statement also covers isolated points of a closed sublevel. -/
theorem sublevel_interval_cover_of_boundary_finset
    {S : Set ℝ} {g : ℝ → ℝ} {eps : ℝ}
    (hS : S.OrdConnected) (hg : ContinuousOn g S)
    (B : Finset ℝ)
    (hB : ∀ x ∈ S, ‖g x‖ = eps → x ∈ B) :
    ∃ t : Finset (Set ℝ), t.card ≤ 2 * B.card + 1 ∧
      (∀ E ∈ t, E.OrdConnected) ∧
      (∀ x, (x ∈ S ∧ ‖g x‖ ≤ eps) ↔ ∃ E ∈ t, x ∈ E) := by
  classical
  suffices aux : ∀ n : ℕ, ∀ (S : Set ℝ) (B : Finset ℝ),
      B.card ≤ n → S.OrdConnected → ContinuousOn g S →
      (∀ x ∈ S, ‖g x‖ = eps → x ∈ B) →
      ∃ t : Finset (Set ℝ), t.card ≤ 2 * B.card + 1 ∧
        (∀ E ∈ t, E.OrdConnected) ∧
        (∀ x, (x ∈ S ∧ ‖g x‖ ≤ eps) ↔ ∃ E ∈ t, x ∈ E) by
    exact aux B.card S B le_rfl hS hg hB
  intro n
  induction n with
  | zero =>
    intro S B hcard hS hg hB
    have hb : B = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hcard)
    have hno : ∀ x ∈ S, ‖g x‖ ≠ eps := by
      intro x hx he
      have := hB x hx he
      simpa [hb] using this
    refine ⟨{{x | x ∈ S ∧ ‖g x‖ ≤ eps}}, ?_, ?_, ?_⟩
    · simp
    · intro E hE
      have heq : E = {x | x ∈ S ∧ ‖g x‖ ≤ eps} := Finset.mem_singleton.mp hE
      subst E
      exact sublevel_ordConnected_of_no_level hS hg hno
    · intro x
      simp
  | succ n ih =>
    intro S B hcard hS hg hB
    by_cases hb : B = ∅
    · have hno : ∀ x ∈ S, ‖g x‖ ≠ eps := by
        intro x hx he
        have := hB x hx he
        simpa [hb] using this
      refine ⟨{{x | x ∈ S ∧ ‖g x‖ ≤ eps}}, ?_, ?_, ?_⟩
      · simp
      · intro E hE
        have heq := Finset.mem_singleton.mp hE
        subst E
        exact sublevel_ordConnected_of_no_level hS hg hno
      · intro x
        simp
    · obtain ⟨c, hc⟩ := Finset.nonempty_iff_ne_empty.mpr hb
      let BL := B.filter (fun x => x < c)
      let BR := B.filter (fun x => c < x)
      have hBL : BL ⊆ B.erase c := by
        intro x hx
        obtain ⟨hxB, hxc⟩ := Finset.mem_filter.mp hx
        exact Finset.mem_erase.mpr ⟨ne_of_lt hxc, hxB⟩
      have hBR : BR ⊆ B.erase c := by
        intro x hx
        obtain ⟨hxB, hcx⟩ := Finset.mem_filter.mp hx
        exact Finset.mem_erase.mpr ⟨ne_of_gt hcx, hxB⟩
      have herase : (B.erase c).card + 1 = B.card := B.card_erase_add_one hc
      have hlcard : BL.card ≤ n := by
        have := Finset.card_le_card hBL
        omega
      have hrcard : BR.card ≤ n := by
        have := Finset.card_le_card hBR
        omega
      have hdis : Disjoint BL BR := by
        apply Finset.disjoint_left.mpr
        intro x hx hy
        exact (lt_asymm (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2)
      have hcount : BL.card + BR.card + 1 ≤ B.card := by
        have hu : BL ∪ BR ⊆ B.erase c := Finset.union_subset hBL hBR
        have hh := Finset.card_le_card hu
        rw [Finset.card_union_of_disjoint hdis] at hh
        omega
      obtain ⟨tl, htl, hlconn, hlcov⟩ := ih (S ∩ Iio c) BL hlcard
        (hS.inter ordConnected_Iio) (hg.mono inter_subset_left)
        (by intro x hx he; exact Finset.mem_filter.mpr ⟨hB x hx.1 he, hx.2⟩)
      obtain ⟨tr, htr, hrconn, hrcov⟩ := ih (S ∩ Ioi c) BR hrcard
        (hS.inter ordConnected_Ioi) (hg.mono inter_subset_left)
        (by intro x hx he; exact Finset.mem_filter.mpr ⟨hB x hx.1 he, hx.2⟩)
      let C : Set ℝ := {x | x = c ∧ x ∈ S ∧ ‖g x‖ ≤ eps}
      have hCconn : C.OrdConnected := by
        constructor
        intro x hx y hy z hz
        have hzc : z = c := by
          have hxc := hx.1
          have hyc := hy.1
          have := hz.1
          have := hz.2
          linarith
        exact ⟨hzc, hzc.symm ▸ (hx.1 ▸ hx.2)⟩
      refine ⟨insert C (tl ∪ tr), ?_, ?_, ?_⟩
      · have h1 := Finset.card_insert_le C (tl ∪ tr)
        have h2 := Finset.card_union_le tl tr
        omega
      · intro E hE
        rcases Finset.mem_insert.mp hE with rfl | hE
        · exact hCconn
        · rcases Finset.mem_union.mp hE with hE | hE
          · exact hlconn E hE
          · exact hrconn E hE
      · intro x
        constructor
        · intro hx
          rcases lt_trichotomy x c with h | h | h
          · obtain ⟨E, hE, hxE⟩ := (hlcov x).mp ⟨⟨hx.1,h⟩,hx.2⟩
            exact ⟨E, Finset.mem_insert_of_mem (Finset.mem_union_left _ hE), hxE⟩
          · exact ⟨C, Finset.mem_insert_self _ _, h, hx⟩
          · obtain ⟨E, hE, hxE⟩ := (hrcov x).mp ⟨⟨hx.1,h⟩,hx.2⟩
            exact ⟨E, Finset.mem_insert_of_mem (Finset.mem_union_right _ hE), hxE⟩
        · rintro ⟨E,hE,hxE⟩
          rcases Finset.mem_insert.mp hE with rfl | hE
          · exact hxE.2
          · rcases Finset.mem_union.mp hE with hE | hE
            · have hx := (hlcov x).mpr ⟨E,hE,hxE⟩
              exact ⟨hx.1.1,hx.2⟩
            · have hx := (hrcov x).mpr ⟨E,hE,hxE⟩
              exact ⟨hx.1.1,hx.2⟩

/-- A derivative lower bound gives an explicit finite interval cover of
the closed sublevel, including any singleton components. -/
theorem sublevel_interval_cover_of_derivative_bound
    {g : ℝ → ℝ} {k : ℕ} {a b eps lam : ℝ}
    (hk : 0 < k)
    (hcont : ∀ r : ℕ, ContinuousOn (iteratedDeriv r g) (Icc a b))
    (hlam : 0 < lam)
    (hlow : ∀ x ∈ Icc a b, lam ≤ |iteratedDeriv k g x|) :
    ∃ t : Finset (Set ℝ), t.card ≤ 4 * k + 1 ∧
      (∀ E ∈ t, E.OrdConnected) ∧
      (∀ x, (x ∈ Icc a b ∧ ‖g x‖ ≤ eps) ↔ ∃ E ∈ t, x ∈ E) := by
  classical
  obtain ⟨hfin,hcard⟩ := abs_boundary_set_finite_and_ncard_le
    (eps := eps) hk hcont hlam hlow
  obtain ⟨t,ht,hconn,hcov⟩ := sublevel_interval_cover_of_boundary_finset
    ordConnected_Icc (by simpa using hcont 0) hfin.toFinset
    (by intro x hx he; exact hfin.mem_toFinset.mpr ⟨hx, by simpa [Real.norm_eq_abs] using he⟩)
  refine ⟨t, ?_, hconn, hcov⟩
  have hb : hfin.toFinset.card ≤ 2 * k := by
    rw [← Set.ncard_eq_toFinset_card _ hfin]
    exact hcard
  omega

end MahlerLean
