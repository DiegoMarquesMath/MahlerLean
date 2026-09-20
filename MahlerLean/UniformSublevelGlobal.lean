import MahlerLean.UniformIntervalCover
import MahlerLean.FiniteSublevelAssembly

/-!
Global uniform sublevel measure bound.

This module clips the compact source intervals extracted from the product
cover to the fixed source interval and feeds them into the finite assembly
theorem.  Zero-order patches are included automatically.
-/

open Set
open MeasureTheory

noncomputable section
namespace MahlerLean

/-- Uniform global sublevel measure estimate for normalized analytic
linear combinations under Wronskian nondegeneracy. -/
theorem exists_uniform_analytic_sublevel_measure_bound
    {N : ℕ}
    (hN : 2 ≤ N)
    (φ : Fin N → ℝ → ℝ)
    {U : Set ℝ}
    (hU : IsOpen U)
    (hφ : ∀ j, AnalyticOnNhd ℝ (φ j) U)
    {A B : ℝ}
    (hAB : A ≤ B)
    (hJU : Icc A B ⊆ U)
    (hW : ∀ x ∈ Icc A B, wronskian φ x ≠ 0) :
    ∃ lam : ℝ,
      0 < lam ∧
      ∃ L : ℕ,
        ∀ c : EuclideanSpace ℝ (Fin N),
          ‖c‖ = 1 →
          ∀ eps : ℝ,
            0 ≤ eps →
            eps < lam →
            volume.real
                {x : ℝ |
                  x ∈ Icc A B ∧
                    ‖jetLinearCombo φ c x‖ ≤ eps}
              ≤
                (L : ℝ) *
                  (2 * (((N - 1 : ℕ) : ℝ)) *
                    (2 * (((N - 1 : ℕ) : ℝ)) + 1) *
                    (eps / lam) ^
                      (((((N - 1 : ℕ) : ℝ)))⁻¹)) := by
  classical

  have hNpos : 0 < N := by
    omega

  obtain
    ⟨eta, heta, k, C, a, b,
      hC, _hcenter, hIU, hbound, t, hcover⟩ :=
    exists_finite_uniform_jet_interval_cover_of_analytic
      hNpos φ hU hφ isCompact_Icc hJU hW

  refine ⟨eta / 2, by linarith, t.card, ?_⟩

  intro c hc eps heps hepslam

  let s : Finset (coefficientSourceProduct N (Icc A B)) :=
    t.filter fun p =>
      c ∈ C p ∧
        max A (a p) ≤ min B (b p)

  have hcover' :
      Icc A B ⊆
        ⋃ p ∈ s,
          Icc (max A (a p)) (min B (b p)) := by
    intro x hx

    have hq :
        (c, x) ∈ coefficientSourceProduct N (Icc A B) :=
      (mem_coefficientSourceProduct
        (K := Icc A B) (c, x)).2 ⟨hc, hx⟩

    obtain ⟨p, hpt, hcp, hxp⟩ :=
      hcover (c, x) hq

    have hleft :
        max A (a p) ≤ x :=
      max_le hx.1 hxp.1.le

    have hright :
        x ≤ min B (b p) :=
      le_min hx.2 hxp.2.le

    have hpnonempty :
        max A (a p) ≤ min B (b p) :=
      hleft.trans hright

    have hps : p ∈ s := by
      simp [s, hpt, hcp, hpnonempty]

    exact
      Set.mem_iUnion₂.mpr
        ⟨p, hps, hleft, hright⟩

  have hsub' :
      ∀ p ∈ s,
        Icc (max A (a p)) (min B (b p))
          ⊆ Icc A B := by
    intro p hp x hx
    exact
      ⟨(le_max_left A (a p)).trans hx.1,
        hx.2.trans (min_le_left B (b p))⟩

  have hab' :
      ∀ p ∈ s,
        max A (a p) ≤ min B (b p) := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2.2

  have hIU' :
      ∀ p ∈ s,
        Icc (max A (a p)) (min B (b p))
          ⊆ U := by
    intro p hp x hx
    apply hIU p
    exact
      ⟨(le_max_right A (a p)).trans hx.1,
        hx.2.trans (min_le_right B (b p))⟩

  have hlow' :
      ∀ p ∈ s,
        ∀ x ∈ Icc (max A (a p)) (min B (b p)),
          eta / 2 ≤ |jetApply φ c (k p) x| := by
    intro p hp x hx

    have hcp : c ∈ C p :=
      (Finset.mem_filter.mp hp).2.1

    apply hbound p c hcp x
    exact
      ⟨(le_max_right A (a p)).trans hx.1,
        hx.2.trans (min_le_right B (b p))⟩

  have hsmall :=
    jetLinearCombo_sublevel_measure_bound_of_finite_interval_cover_all_orders
      hN φ c hφ s
        (fun p => max A (a p))
        (fun p => min B (b p))
        k hcover' hsub' hab' hIU'
        heps (by linarith) hepslam hlow'

  have hcardNat : s.card ≤ t.card :=
    Finset.card_filter_le _ _

  have hcard :
      (s.card : ℝ) ≤ (t.card : ℝ) := by
    exact_mod_cast hcardNat

  have hfactor :
      0 ≤
        2 * (((N - 1 : ℕ) : ℝ)) *
          (2 * (((N - 1 : ℕ) : ℝ)) + 1) *
          (eps / (eta / 2)) ^
            (((((N - 1 : ℕ) : ℝ)))⁻¹) := by
    positivity

  exact
    hsmall.trans
      (mul_le_mul_of_nonneg_right hcard hfactor)

end MahlerLean
