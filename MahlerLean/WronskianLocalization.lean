import MahlerLean.AnalyticLocalization
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
The manuscript's Wronskians, analyticity, and compact localization.
Non-identical vanishing of each Wronskian remains an explicit hypothesis.
The implication from nonrationality of f is not yet formalized.
-/

noncomputable section
namespace MahlerLean

open Set

/-- The ordinary Wronskian, with derivative orders 0,...,N-1 as rows. -/
def wronskian {N : ℕ} (φ : Fin N → ℝ → ℝ) (x : ℝ) : ℝ :=
  Matrix.det (fun k j : Fin N => iteratedDeriv k.val (φ j) x)

/-- Finite determinants of analytic derivatives are analytic. -/
theorem wronskian_analytic {N : ℕ} (φ : Fin N → ℝ → ℝ) {U : Set ℝ}
    (hφ : ∀ j, AnalyticOnNhd ℝ (φ j) U) :
    AnalyticOnNhd ℝ (wronskian φ) U := by
  have hd (k j : Fin N) : AnalyticOnNhd ℝ (iteratedDeriv k.val (φ j)) U := by
    rw [iteratedDeriv_eq_iterate]
    exact (hφ j).iterated_deriv k.val
  unfold wronskian
  simp only [Matrix.det_apply']
  apply Finset.analyticOnNhd_fun_sum
  intro σ _
  exact analyticOnNhd_const.mul
    (Finset.analyticOnNhd_fun_prod _ fun j _ => hd (σ j) j)

/-- Lexicographic order (0,0),(0,1),(1,0),(1,1),...,(d,1). -/
def rationalFamily (f : ℝ → ℝ) (d : ℕ) (j : Fin (2 * (d + 1))) (x : ℝ) : ℝ :=
  x ^ (j.val / 2) * f x ^ (j.val % 2)

/-- The analytic family x^i f(x)^j used in the manuscript. -/
theorem rationalFamily_analytic {f : ℝ → ℝ} {U : Set ℝ}
    (hf : AnalyticOnNhd ℝ f U) (d : ℕ) (j : Fin (2 * (d + 1))) :
    AnalyticOnNhd ℝ (rationalFamily f d j) U := by
  exact (analyticOnNhd_id.pow _).mul (hf.pow _)

/-- W_d for the manuscript's target-degree-one family. -/
def rationalWronskian (f : ℝ → ℝ) (d : ℕ) : ℝ → ℝ :=
  wronskian (rationalFamily f d)

theorem rationalWronskian_analytic {f : ℝ → ℝ} {U : Set ℝ}
    (hf : AnalyticOnNhd ℝ f U) (d : ℕ) :
    AnalyticOnNhd ℝ (rationalWronskian f d) U :=
  wronskian_analytic _ (rationalFamily_analytic hf d)

/-- The compact-zero conclusion of the manuscript's corollary, conditional
on the still-pending nontriviality of W_d. -/
theorem rationalWronskian_zeros_finite
    {f : ℝ → ℝ} {U K : Set ℝ} (hf : AnalyticOnNhd ℝ f U)
    (hU : IsPreconnected U) (d : ℕ)
    (hnonzero : ∃ y ∈ U, rationalWronskian f d y ≠ 0)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    {x ∈ K | rationalWronskian f d x = 0}.Finite :=
  analytic_zeros_finite_on_compact (rationalWronskian_analytic hf d)
    hU hnonzero hK hKU

/-- A finite set containing exactly the zeros of all specified degrees. -/
theorem exists_rationalWronskian_zero_finset
    {f : ℝ → ℝ} {U K : Set ℝ} (hf : AnalyticOnNhd ℝ f U)
    (hU : IsPreconnected U) (D : Finset ℕ)
    (hnonzero : ∀ d ∈ D, ∃ y ∈ U, rationalWronskian f d y ≠ 0)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ Z : Finset ℝ, ∀ x, x ∈ Z ↔
      x ∈ K ∧ ∃ d ∈ D, rationalWronskian f d x = 0 :=
  exists_analytic_zero_finset D (rationalWronskian f) hU hK hKU
    (fun d _ => rationalWronskian_analytic hf d) hnonzero

/-- Simultaneous Wronskian separation on a smaller interval. The degree
set is chosen first; the interval and lower bound can depend on it. -/
theorem exists_interval_rationalWronskians_separated
    {f : ℝ → ℝ} {U : Set ℝ} (hf : AnalyticOnNhd ℝ f U)
    (hU : IsPreconnected U) (D : Finset ℕ)
    (hnonzero : ∀ d ∈ D, ∃ y ∈ U, rationalWronskian f d y ≠ 0)
    (a b : ℝ) (hab : a < b) (hI : Icc a b ⊆ U) :
    ∃ l u δ : ℝ, a < l ∧ l < u ∧ u < b ∧ 0 < δ ∧
      ∀ d ∈ D, ∀ x ∈ Icc l u, δ ≤ |rationalWronskian f d x| :=
  exists_interval_analytic_family_separated D (rationalWronskian f) hU
    (fun d _ => rationalWronskian_analytic hf d) hnonzero a b hab hI

end MahlerLean
