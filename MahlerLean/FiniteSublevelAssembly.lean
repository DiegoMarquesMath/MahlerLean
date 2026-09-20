import MahlerLean.LocalUniformSublevel
import Mathlib.MeasureTheory.Measure.Real

/-!
Finite assembly of local sublevel estimates.

This module performs the quantitative part of the global Step 12
argument.  It first replaces the exponent attached to a varying positive
derivative order by the common exponent `1 / (N - 1)`.  It then sums
local estimates over a finite interval cover.

The remaining topological step is to extract interval patches satisfying
the hypotheses below from the finite coefficient/source product cover.
-/

open Set
open MeasureTheory

noncomputable section
namespace MahlerLean

/-- For a base in `[0,1]`, replacing a positive denominator by a larger
one makes the reciprocal-power bound weaker. -/
theorem rpow_inv_nat_le_rpow_inv_nat
    {x : ℝ} {k n : ℕ}
    (hx0 : 0 ≤ x)
    (hx1 : x ≤ 1)
    (hk : 0 < k)
    (hkn : k ≤ n) :
    x ^ (((k : ℝ))⁻¹) ≤ x ^ (((n : ℝ))⁻¹) := by
  have hkR : 0 < (k : ℝ) := by
    exact_mod_cast hk
  have hknR : (k : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hkn
  have hexp :
      ((n : ℝ))⁻¹ ≤ ((k : ℝ))⁻¹ := by
    simpa [one_div] using
      (one_div_le_one_div_of_le hkR hknR)
  have hn0 : 0 ≤ ((n : ℝ))⁻¹ := by
    positivity
  exact
    Real.rpow_le_rpow_of_exponent_ge'
      hx0 hx1 hn0 hexp

/-- A positive-order local estimate may be written with the common
exponent `1 / (N - 1)`, uniformly over all `k : Fin N`. -/
theorem jetLinearCombo_sublevel_measure_bound_uniform_order
    {N : ℕ}
    (hN : 2 ≤ N)
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
    (hepslam : eps ≤ lam)
    (hlow :
      ∀ x ∈ Icc a b,
        lam ≤ |jetApply φ c k x|) :
    volume.real
        {x : ℝ |
          x ∈ Icc a b ∧
            ‖jetLinearCombo φ c x‖ ≤ eps}
      ≤
        2 * (((N - 1 : ℕ) : ℝ)) *
          (2 * (((N - 1 : ℕ) : ℝ)) + 1) *
          (eps / lam) ^ (((((N - 1 : ℕ) : ℝ)))⁻¹) := by

  have hkN : k.val ≤ N - 1 := by
    omega

  have hratio0 : 0 ≤ eps / lam :=
    div_nonneg heps hlam.le

  have hratio1 : eps / lam ≤ 1 :=
    (div_le_one hlam).2 hepslam

  have hrpow :
      (eps / lam) ^ (((k.val : ℝ))⁻¹)
        ≤
      (eps / lam) ^ (((((N - 1 : ℕ) : ℝ)))⁻¹) :=
    rpow_inv_nat_le_rpow_inv_nat
      hratio0 hratio1 hk hkN

  have hkR :
      (k.val : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := by
    exact_mod_cast hkN

  have hk0 : 0 ≤ (k.val : ℝ) := by
    positivity

  have hn0 : 0 ≤ ((N - 1 : ℕ) : ℝ) := by
    positivity

  have hcoeff :
      2 * (k.val : ℝ) *
          (2 * (k.val : ℝ) + 1)
        ≤
      2 * (((N - 1 : ℕ) : ℝ)) *
          (2 * (((N - 1 : ℕ) : ℝ)) + 1) := by
    nlinarith

  have hlocal :=
    jetLinearCombo_sublevel_measure_bound
      φ c hφ k hk hab hI heps hlam hlow

  calc
    volume.real
        {x : ℝ |
          x ∈ Icc a b ∧
            ‖jetLinearCombo φ c x‖ ≤ eps}
      ≤
        (2 * (k.val : ℝ) *
          (2 * (k.val : ℝ) + 1)) *
          (eps / lam) ^ (((k.val : ℝ))⁻¹) := by
            simpa [mul_assoc] using hlocal
    _ ≤
        (2 * (((N - 1 : ℕ) : ℝ)) *
          (2 * (((N - 1 : ℕ) : ℝ)) + 1)) *
          (eps / lam) ^ (((((N - 1 : ℕ) : ℝ)))⁻¹) := by
            exact
              mul_le_mul hcoeff hrpow
                (by positivity) (by positivity)
    _ =
        2 * (((N - 1 : ℕ) : ℝ)) *
          (2 * (((N - 1 : ℕ) : ℝ)) + 1) *
          (eps / lam) ^ (((((N - 1 : ℕ) : ℝ)))⁻¹) := by
            ring

/-- Finite-cover summation for a real-valued measure.  The two inclusion
hypotheses identify `S` with the finite union of the local pieces. -/
theorem measureReal_le_card_mul_of_finite_cover
    {ι : Type*}
    (t : Finset ι)
    (S : Set ℝ)
    (E : ι → Set ℝ)
    (B : ℝ)
    (hcover : S ⊆ ⋃ i ∈ t, E i)
    (hsub : ∀ i ∈ t, E i ⊆ S)
    (hlocal : ∀ i ∈ t, volume.real (E i) ≤ B) :
    volume.real S ≤ (t.card : ℝ) * B := by
  classical

  have hEq : S = ⋃ i ∈ t, E i := by
    apply Set.Subset.antisymm hcover
    intro x hx
    rcases Set.mem_iUnion₂.mp hx with ⟨i, hi, hxi⟩
    exact hsub i hi hxi

  rw [hEq]

  calc
    volume.real (⋃ i ∈ t, E i)
      ≤ ∑ i ∈ t, volume.real (E i) :=
        measureReal_biUnion_finset_le t E
    _ ≤ ∑ i ∈ t, B := by
      exact Finset.sum_le_sum fun i hi => hlocal i hi
    _ = (t.card : ℝ) * B := by
      simp

/-- Global measure estimate obtained from finitely many interval patches.
The derivative order may vary from patch to patch, but the resulting
exponent and coefficient are uniform. -/
theorem jetLinearCombo_sublevel_measure_bound_of_finite_interval_cover
    {ι : Type*}
    {N : ℕ}
    (hN : 2 ≤ N)
    (φ : Fin N → ℝ → ℝ)
    (c : EuclideanSpace ℝ (Fin N))
    {U : Set ℝ}
    (hφ : ∀ j, AnalyticOnNhd ℝ (φ j) U)
    {A B eps lam : ℝ}
    (t : Finset ι)
    (a b : ι → ℝ)
    (k : ι → Fin N)
    (hcover :
      Icc A B ⊆ ⋃ i ∈ t, Icc (a i) (b i))
    (hsub :
      ∀ i ∈ t, Icc (a i) (b i) ⊆ Icc A B)
    (hab :
      ∀ i ∈ t, a i ≤ b i)
    (hIU :
      ∀ i ∈ t, Icc (a i) (b i) ⊆ U)
    (hk :
      ∀ i ∈ t, 0 < (k i).val)
    (heps : 0 ≤ eps)
    (hlam : 0 < lam)
    (hepslam : eps ≤ lam)
    (hlow :
      ∀ i ∈ t,
        ∀ x ∈ Icc (a i) (b i),
          lam ≤ |jetApply φ c (k i) x|) :
    volume.real
        {x : ℝ |
          x ∈ Icc A B ∧
            ‖jetLinearCombo φ c x‖ ≤ eps}
      ≤
        (t.card : ℝ) *
          (2 * (((N - 1 : ℕ) : ℝ)) *
            (2 * (((N - 1 : ℕ) : ℝ)) + 1) *
            (eps / lam) ^ (((((N - 1 : ℕ) : ℝ)))⁻¹)) := by
  classical

  let S : Set ℝ :=
    {x : ℝ |
      x ∈ Icc A B ∧
        ‖jetLinearCombo φ c x‖ ≤ eps}

  let E : ι → Set ℝ :=
    fun i =>
      {x : ℝ |
        x ∈ Icc (a i) (b i) ∧
          ‖jetLinearCombo φ c x‖ ≤ eps}

  apply
    measureReal_le_card_mul_of_finite_cover
      t S E
        (2 * (((N - 1 : ℕ) : ℝ)) *
          (2 * (((N - 1 : ℕ) : ℝ)) + 1) *
          (eps / lam) ^ (((((N - 1 : ℕ) : ℝ)))⁻¹))

  · intro x hx
    rcases Set.mem_iUnion₂.mp (hcover hx.1) with ⟨i, hi, hxi⟩
    exact
      Set.mem_iUnion₂.mpr
        ⟨i, hi, hxi, hx.2⟩

  · intro i hi x hx
    exact ⟨hsub i hi hx.1, hx.2⟩

  · intro i hi
    exact
      jetLinearCombo_sublevel_measure_bound_uniform_order
        hN φ c hφ (k i) (hk i hi) (hab i hi)
          (hIU i hi) heps hlam hepslam (hlow i hi)


/-- Uniform local measure bound valid for every jet order.  The order-zero
case gives an empty sublevel; positive orders use the common exponent
`1 / (N - 1)`. -/
theorem jetLinearCombo_sublevel_measure_bound_uniform
    {N : ℕ}
    (hN : 2 ≤ N)
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
    volume.real
        {x : ℝ |
          x ∈ Icc a b ∧
            ‖jetLinearCombo φ c x‖ ≤ eps}
      ≤
        2 * (((N - 1 : ℕ) : ℝ)) *
          (2 * (((N - 1 : ℕ) : ℝ)) + 1) *
          (eps / lam) ^ (((((N - 1 : ℕ) : ℝ)))⁻¹) := by

  by_cases hk0 : k.val = 0
  · have hEmpty :=
      jetLinearCombo_sublevel_eq_empty_of_zero_order
        φ c hφ k hk0 hI hepslam hlow
    rw [hEmpty]
    positivity

  · exact
      jetLinearCombo_sublevel_measure_bound_uniform_order
        hN φ c hφ k (Nat.pos_of_ne_zero hk0)
          hab hI heps hlam (le_of_lt hepslam) hlow

/-- Finite interval assembly allowing both zero and positive derivative
orders on the patches. -/
theorem jetLinearCombo_sublevel_measure_bound_of_finite_interval_cover_all_orders
    {ι : Type*}
    {N : ℕ}
    (hN : 2 ≤ N)
    (φ : Fin N → ℝ → ℝ)
    (c : EuclideanSpace ℝ (Fin N))
    {U : Set ℝ}
    (hφ : ∀ j, AnalyticOnNhd ℝ (φ j) U)
    {A B eps lam : ℝ}
    (t : Finset ι)
    (a b : ι → ℝ)
    (k : ι → Fin N)
    (hcover :
      Icc A B ⊆ ⋃ i ∈ t, Icc (a i) (b i))
    (hsub :
      ∀ i ∈ t, Icc (a i) (b i) ⊆ Icc A B)
    (hab :
      ∀ i ∈ t, a i ≤ b i)
    (hIU :
      ∀ i ∈ t, Icc (a i) (b i) ⊆ U)
    (heps : 0 ≤ eps)
    (hlam : 0 < lam)
    (hepslam : eps < lam)
    (hlow :
      ∀ i ∈ t,
        ∀ x ∈ Icc (a i) (b i),
          lam ≤ |jetApply φ c (k i) x|) :
    volume.real
        {x : ℝ |
          x ∈ Icc A B ∧
            ‖jetLinearCombo φ c x‖ ≤ eps}
      ≤
        (t.card : ℝ) *
          (2 * (((N - 1 : ℕ) : ℝ)) *
            (2 * (((N - 1 : ℕ) : ℝ)) + 1) *
            (eps / lam) ^ (((((N - 1 : ℕ) : ℝ)))⁻¹)) := by
  classical

  let S : Set ℝ :=
    {x : ℝ |
      x ∈ Icc A B ∧
        ‖jetLinearCombo φ c x‖ ≤ eps}

  let E : ι → Set ℝ :=
    fun i =>
      {x : ℝ |
        x ∈ Icc (a i) (b i) ∧
          ‖jetLinearCombo φ c x‖ ≤ eps}

  apply
    measureReal_le_card_mul_of_finite_cover
      t S E
        (2 * (((N - 1 : ℕ) : ℝ)) *
          (2 * (((N - 1 : ℕ) : ℝ)) + 1) *
          (eps / lam) ^ (((((N - 1 : ℕ) : ℝ)))⁻¹))

  · intro x hx
    rcases Set.mem_iUnion₂.mp (hcover hx.1) with
      ⟨i, hi, hxi⟩
    exact
      Set.mem_iUnion₂.mpr
        ⟨i, hi, hxi, hx.2⟩

  · intro i hi x hx
    exact ⟨hsub i hi hx.1, hx.2⟩

  · intro i hi
    exact
      jetLinearCombo_sublevel_measure_bound_uniform
        hN φ c hφ (k i) (hab i hi)
          (hIU i hi) heps hlam hepslam (hlow i hi)

end MahlerLean
