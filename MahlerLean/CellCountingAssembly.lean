import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
Finite-cover assembly for Proposition 5.1. Covers may overlap: multiple
witnesses for one source center only cause admissible overcounting.
The last lemma absorbs a logarithmic number of large target blocks into
the exponent gap 17/10 - 33/20 = 1/20.
-/
open scoped BigOperators
open Filter
namespace MahlerLean

/-- Sum local bounds without requiring disjoint cells or unique witnesses. -/
theorem card_le_sum_of_finite_cover {α ι : Type*} [DecidableEq α]
    (S : Finset α) (t : Finset ι) (E : ι → Finset α) (b : ι → ℝ)
    (hcover : ∀ x ∈ S, ∃ i ∈ t, x ∈ E i)
    (hbound : ∀ i ∈ t, ((E i).card : ℝ) ≤ b i) :
    (S.card : ℝ) ≤ ∑ i ∈ t, b i := by
  classical
  have hsub : S ⊆ t.biUnion E := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := hcover x hx
    exact Finset.mem_biUnion.mpr ⟨i, hi, hxi⟩
  have hn : S.card ≤ ∑ i ∈ t, (E i).card :=
    (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hr : (S.card : ℝ) ≤ ∑ i ∈ t, ((E i).card : ℝ) := by
    exact_mod_cast hn
  exact hr.trans (Finset.sum_le_sum hbound)

/-- Uniform per-cell bounds multiplied by a bound for the number of cells. -/
theorem card_le_of_uniform_cell_bound {α ι : Type*} [DecidableEq α]
    (S : Finset α) (t : Finset ι) (E : ι → Finset α)
    {B M : ℝ} (hB : 0 ≤ B) (ht : (t.card : ℝ) ≤ M)
    (hcover : ∀ x ∈ S, ∃ i ∈ t, x ∈ E i)
    (hbound : ∀ i ∈ t, ((E i).card : ℝ) ≤ B) :
    (S.card : ℝ) ≤ M * B := by
  have h := card_le_sum_of_finite_cover S t E (fun _ ↦ B) hcover hbound
  simp only [Finset.sum_const, nsmul_eq_mul] at h
  exact h.trans (mul_le_mul_of_nonneg_right ht hB)

/-- The logarithmic loss in the large-block sum fits in the manuscript's
exponent 17/10. The threshold here is independent of a lower target cutoff. -/
theorem eventually_log_mul_large_block_power_le :
    ∀ᶠ Q : ℝ in atTop,
      Real.log Q * Q ^ ((33 : ℝ) / 20) ≤ Q ^ ((17 : ℝ) / 10) := by
  have h := (isLittleO_log_rpow_atTop (r := (1 : ℝ) / 20)
    (by norm_num)).bound (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [h, eventually_gt_atTop (0 : ℝ)] with Q hQ hpos
  have hlog : Real.log Q ≤ Q ^ ((1 : ℝ) / 20) := by
    simpa only [one_mul, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hpos _)] using
      (le_abs_self (Real.log Q)).trans hQ
  calc
    Real.log Q * Q ^ ((33 : ℝ) / 20) ≤
        Q ^ ((1 : ℝ) / 20) * Q ^ ((33 : ℝ) / 20) :=
      mul_le_mul_of_nonneg_right hlog (Real.rpow_nonneg hpos.le _)
    _ = Q ^ ((17 : ℝ) / 10) := by
      rw [← Real.rpow_add hpos]
      norm_num

end MahlerLean
