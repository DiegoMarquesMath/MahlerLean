import MahlerLean.FiniteJetCover
import MahlerLean.SublevelOneDim

/-!
Local uniform sublevel bounds for analytic linear combinations.

This module is the next bridge in Step 12.  On an interval carrying one
fixed jet-coordinate lower bound, it applies the one-dimensional estimate
from Step 11 to the analytic linear combination from Step 12a.  The
zero-order case is separated explicitly: for a sublevel below the lower
bound, the local sublevel set is empty.
-/

open Set
open MeasureTheory

noncomputable section
namespace MahlerLean

/-- A strict absolute lower bound makes the corresponding smaller sublevel
set empty.  This is the order-zero branch of the uniform jet argument. -/
theorem sublevel_set_eq_empty_of_abs_lower_bound
    {g : ℝ → ℝ} {a b eps lam : ℝ}
    (hepslam : eps < lam)
    (hlow : ∀ x ∈ Icc a b, lam ≤ |g x|) :
    {x : ℝ | x ∈ Icc a b ∧ ‖g x‖ ≤ eps} = ∅ := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro hx
  have hnorm : |g x| ≤ eps := by
    simpa [Real.norm_eq_abs] using hx.2
  have hlower := hlow x hx.1
  linarith

/-- Measure-zero form of the order-zero sublevel exclusion. -/
theorem sublevel_measure_eq_zero_of_abs_lower_bound
    {g : ℝ → ℝ} {a b eps lam : ℝ}
    (hepslam : eps < lam)
    (hlow : ∀ x ∈ Icc a b, lam ≤ |g x|) :
    volume.real {x : ℝ | x ∈ Icc a b ∧ ‖g x‖ ≤ eps} = 0 := by
  rw [sublevel_set_eq_empty_of_abs_lower_bound hepslam hlow]
  simp

/-- On one interval where a positive-order jet coordinate is uniformly
large, the analytic linear combination satisfies the explicit Step 11
sublevel estimate. -/
theorem jetLinearCombo_sublevel_measure_bound
    {N : ℕ}
    (φ : Fin N → ℝ → ℝ)
    (c : EuclideanSpace ℝ (Fin N))
    {U : Set ℝ}
    (hφ : ∀ j, AnalyticOnNhd ℝ (φ j) U)
    {a b eps lam : ℝ}
    (k : Fin N)
    (hk : 0 < k.val)
    (hab : a ≤ b)
    (hI : Icc a b ⊆ U)
    (heps : 0 ≤ eps)
    (hlam : 0 < lam)
    (hlow :
      ∀ x ∈ Icc a b,
        lam ≤ |jetApply φ c k x|) :
    volume.real
        {x : ℝ |
          x ∈ Icc a b ∧
            ‖jetLinearCombo φ c x‖ ≤ eps}
      ≤
        2 * (k.val : ℝ) *
          (2 * (k.val : ℝ) + 1) *
          (eps / lam) ^ (((k.val : ℝ))⁻¹) := by

  obtain ⟨hcont, hdiff⟩ :=
    analyticFamily_linearCombo_smooth φ c hφ hI

  apply
    sublevel_measure_bound
      (g := jetLinearCombo φ c)
      (k := k.val)
      (a := a) (b := b)
      (eps := eps) (lam := lam)
      hk hab hcont hdiff heps hlam

  intro x hx
  rw [
    iteratedDeriv_jetLinearCombo_eq_jetApply
      φ c hφ (hI hx) k
  ]
  exact hlow x hx

/-- If the selected jet coordinate has order zero, the local sublevel set
is empty below the jet lower bound. -/
theorem jetLinearCombo_sublevel_eq_empty_of_zero_order
    {N : ℕ}
    (φ : Fin N → ℝ → ℝ)
    (c : EuclideanSpace ℝ (Fin N))
    {U : Set ℝ}
    (hφ : ∀ j, AnalyticOnNhd ℝ (φ j) U)
    {a b eps lam : ℝ}
    (k : Fin N)
    (hk : k.val = 0)
    (hI : Icc a b ⊆ U)
    (hepslam : eps < lam)
    (hlow :
      ∀ x ∈ Icc a b,
        lam ≤ |jetApply φ c k x|) :
    {x : ℝ |
      x ∈ Icc a b ∧
        ‖jetLinearCombo φ c x‖ ≤ eps} = ∅ := by

  apply sublevel_set_eq_empty_of_abs_lower_bound hepslam
  intro x hx

  have hEq :=
    iteratedDeriv_jetLinearCombo_eq_jetApply
      φ c hφ (hI hx) k

  calc
    lam ≤ |jetApply φ c k x| := hlow x hx
    _ = |iteratedDeriv k.val (jetLinearCombo φ c) x| :=
      congrArg abs hEq.symm
    _ = |jetLinearCombo φ c x| := by
      simp [hk]

/-- Complete local dichotomy for a selected jet coordinate: order zero
gives an empty sublevel, while positive order gives the explicit measure
bound. -/
theorem jetLinearCombo_local_sublevel_control
    {N : ℕ}
    (φ : Fin N → ℝ → ℝ)
    (c : EuclideanSpace ℝ (Fin N))
    {U : Set ℝ}
    (hφ : ∀ j, AnalyticOnNhd ℝ (φ j) U)
    {a b eps lam : ℝ}
    (k : Fin N)
    (hab : a ≤ b)
    (hI : Icc a b ⊆ U)
    (heps : 0 ≤ eps)
    (hlam : 0 < lam)
    (hepslam : eps < lam)
    (hlow :
      ∀ x ∈ Icc a b,
        lam ≤ |jetApply φ c k x|) :
    (k.val = 0 ∧
      {x : ℝ |
        x ∈ Icc a b ∧
          ‖jetLinearCombo φ c x‖ ≤ eps} = ∅)
      ∨
    (0 < k.val ∧
      volume.real
          {x : ℝ |
            x ∈ Icc a b ∧
              ‖jetLinearCombo φ c x‖ ≤ eps}
        ≤
          2 * (k.val : ℝ) *
            (2 * (k.val : ℝ) + 1) *
            (eps / lam) ^ (((k.val : ℝ))⁻¹)) := by

  by_cases hk0 : k.val = 0
  · left
    exact
      ⟨hk0,
        jetLinearCombo_sublevel_eq_empty_of_zero_order
          φ c hφ k hk0 hI hepslam hlow⟩
  · right
    have hkpos : 0 < k.val := Nat.pos_of_ne_zero hk0
    exact
      ⟨hkpos,
        jetLinearCombo_sublevel_measure_bound
          φ c hφ k hkpos hab hI heps hlam hlow⟩

end MahlerLean
