import MahlerLean.UniformDisjointSublevel
import MahlerLean.UniformSublevelGlobal

/-!
Uniform analytic sublevel bounds with an exact pairwise-disjoint interval
decomposition.  This is the form consumed directly by the Farey-counting
theorem.
-/

open Set MeasureTheory

noncomputable section
namespace MahlerLean

/-- Uniform measure and pairwise-disjoint interval-complexity bounds. -/
theorem exists_uniform_analytic_disjoint_sublevel_bound
    {N : ℕ} (hN : 2 ≤ N) (φ : Fin N → ℝ → ℝ)
    {U : Set ℝ} (hU : IsOpen U) (hφ : ∀ j, AnalyticOnNhd ℝ (φ j) U)
    {A B : ℝ} (hAB : A ≤ B) (hJU : Icc A B ⊆ U)
    (hW : ∀ x ∈ Icc A B, wronskian φ x ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∃ R : ℕ, 0 < R ∧
    ∃ eps0 : ℝ, 0 < eps0 ∧ eps0 < 1 ∧
      ∀ c : EuclideanSpace ℝ (Fin N), ‖c‖ = 1 →
      ∀ eps : ℝ, 0 ≤ eps → eps < eps0 →
        (∃ t : Finset (Set ℝ), t.card ≤ R ∧
          (∀ E ∈ t, E.OrdConnected) ∧
          (t : Set (Set ℝ)).PairwiseDisjoint id ∧
          (∀ x, (x ∈ Icc A B ∧ ‖jetLinearCombo φ c x‖ ≤ eps) ↔
            ∃ E ∈ t, x ∈ E)) ∧
        volume.real {x | x ∈ Icc A B ∧ ‖jetLinearCombo φ c x‖ ≤ eps}
          ≤ C * eps ^ (((N - 1 : ℕ) : ℝ)⁻¹) := by
  obtain ⟨lamM, hlamM, L, hM⟩ :=
    exists_uniform_analytic_sublevel_measure_bound hN φ hU hφ hAB hJU hW
  obtain ⟨lamR, hlamR, R, hR⟩ :=
    exists_uniform_analytic_sublevel_disjoint_interval_cover
      (by omega) φ hU hφ hJU hW
  let p : ℝ := (((N - 1 : ℕ) : ℝ)⁻¹)
  let D : ℝ := (L : ℝ) * (2 * ((N - 1 : ℕ) : ℝ) *
    (2 * ((N - 1 : ℕ) : ℝ) + 1)) / lamM ^ p
  refine ⟨max 1 D, lt_of_lt_of_le zero_lt_one (le_max_left _ _),
    R + 1, by omega, min (1 / 2) (min lamM lamR), ?_, ?_, ?_⟩
  · exact lt_min (by norm_num) (lt_min hlamM hlamR)
  · exact lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  · intro c hc eps heps hsmall
    have heM : eps < lamM := hsmall.trans_le
      ((min_le_right _ _).trans (min_le_left _ _))
    have heR : eps < lamR := hsmall.trans_le
      ((min_le_right _ _).trans (min_le_right _ _))
    constructor
    · obtain ⟨t, ht, hconn, hdis, hcov⟩ := hR c hc eps heR
      exact ⟨t, by omega, hconn, hdis, hcov⟩
    · have hm := hM c hc eps heps heM
      have hp : (eps / lamM) ^ p = eps ^ p / lamM ^ p :=
        Real.div_rpow heps hlamM.le p
      have hm' : volume.real
          {x | x ∈ Icc A B ∧ ‖jetLinearCombo φ c x‖ ≤ eps}
          ≤ D * eps ^ p := by
        change volume.real _ ≤ (L : ℝ) *
          (2 * ((N - 1 : ℕ) : ℝ) * (2 * ((N - 1 : ℕ) : ℝ) + 1) *
            (eps / lamM) ^ p) at hm
        rw [hp] at hm
        simpa only [D, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hm
      exact hm'.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
        (Real.rpow_nonneg heps _))

/-- Rational-family specialization with pairwise-disjoint interval pieces. -/
theorem exists_uniform_rational_relation_disjoint_sublevel_bound
    {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hf : AnalyticOnNhd ℝ f U) (d : ℕ)
    {A B : ℝ} (hAB : A ≤ B) (hJU : Icc A B ⊆ U)
    (hW : ∀ x ∈ Icc A B, rationalWronskian f d x ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∃ R : ℕ, 0 < R ∧
    ∃ eps0 : ℝ, 0 < eps0 ∧ eps0 < 1 ∧
      ∀ c : EuclideanSpace ℝ (Fin (2 * (d + 1))), ‖c‖ = 1 →
      ∀ eps : ℝ, 0 ≤ eps → eps < eps0 →
        (∃ t : Finset (Set ℝ), t.card ≤ R ∧
          (∀ E ∈ t, E.OrdConnected) ∧
          (t : Set (Set ℝ)).PairwiseDisjoint id ∧
          (∀ x, (x ∈ Icc A B ∧
            ‖∑ j, c j * (x ^ (j.val / 2) * f x ^ (j.val % 2))‖ ≤ eps) ↔
              ∃ E ∈ t, x ∈ E)) ∧
        volume.real {x | x ∈ Icc A B ∧
          ‖∑ j, c j * (x ^ (j.val / 2) * f x ^ (j.val % 2))‖ ≤ eps}
          ≤ C * eps ^ (((2 * (d + 1) - 1 : ℕ) : ℝ)⁻¹) := by
  simpa only [jetLinearCombo, rationalFamily] using
    exists_uniform_analytic_disjoint_sublevel_bound
      (by omega : 2 ≤ 2 * (d + 1))
      (rationalFamily f d) hU (rationalFamily_analytic hf d) hAB hJU hW

end MahlerLean
