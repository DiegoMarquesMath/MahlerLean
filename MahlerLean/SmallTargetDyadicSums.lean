import MahlerLean.CellCountingAssembly
import Mathlib.Analysis.SpecificLimits.Basic

open scoped BigOperators
namespace MahlerLean

theorem dyadic_inverse_power_sum_le (t : Finset ℕ) {H : ℝ} (hH : 0 < H) :
    (∑ k ∈ t, (((2 : ℝ)^k*H)^98)⁻¹) ≤ 2*(H^98)⁻¹ := by
  have hterm (k : ℕ) : (((2 : ℝ)^k*H)^98)⁻¹ ≤
      ((1 : ℝ)/2)^k*(H^98)⁻¹ := by
    have hp : (2 : ℝ)^k ≤ ((2 : ℝ)^98)^k :=
      pow_le_pow_left₀ (by norm_num) (by norm_num) k
    have hi := inv_anti₀ (by positivity : (0 : ℝ) < 2^k) hp
    have hh := mul_le_mul_of_nonneg_right hi (by positivity : 0 ≤ (H^98)⁻¹)
    calc
      (((2 : ℝ)^k*H)^98)⁻¹ = (((2 : ℝ)^98)^k)⁻¹*(H^98)⁻¹ := by
        rw [mul_pow, mul_inv_rev, ← pow_mul, Nat.mul_comm k 98, pow_mul]
        ring
      _ ≤ ((1 : ℝ)/2)^k*(H^98)⁻¹ := by simpa only [inv_pow, one_div] using hh
  let n := t.sup id + 1
  have ht : t ⊆ Finset.range n := by
    intro k hk
    apply Finset.mem_range.mpr
    have hh : k ≤ t.sup id := Finset.le_sup (f := id) hk
    dsimp [n]
    omega
  have hsum : (∑ k ∈ t, ((1 : ℝ)/2)^k) ≤ 2 :=
    (Finset.sum_le_sum_of_subset_of_nonneg ht (by intros; positivity)).trans
      (sum_geometric_two_le n)
  calc
    (∑ k ∈ t, (((2 : ℝ)^k*H)^98)⁻¹) ≤
        ∑ k ∈ t, ((1 : ℝ)/2)^k*(H^98)⁻¹ := Finset.sum_le_sum (fun k _ ↦ hterm k)
    _ = (∑ k ∈ t, ((1 : ℝ)/2)^k)*(H^98)⁻¹ := by rw [Finset.sum_mul]
    _ ≤ 2*(H^98)⁻¹ := mul_le_mul_of_nonneg_right hsum (by positivity)

theorem dyadic_square_partial_sum_le (n : ℕ) (H : ℝ) :
    (∑ k ∈ Finset.range (n+1), ((2 : ℝ)^k*H)^2) ≤ 2*((2 : ℝ)^n*H)^2 := by
  induction n with
  | zero =>
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, one_mul, zero_add]
    nlinarith [sq_nonneg H]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    rw [pow_succ (2 : ℝ) n]
    nlinarith [sq_nonneg ((2 : ℝ)^n*H)]

theorem dyadic_square_sum_le (t : Finset ℕ) {H T : ℝ}
    (hH : 0 ≤ H) (ht : ∀ k ∈ t, (2 : ℝ)^k*H < T) :
    (∑ k ∈ t, ((2 : ℝ)^k*H)^2) ≤ 2*T^2 := by
  classical
  by_cases hne : t.Nonempty
  · let n := t.max' hne
    have hsub : t ⊆ Finset.range (n+1) := by
      intro k hk
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (t.le_max' k hk))
    have hh := (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (by intros; positivity)).trans (dyadic_square_partial_sum_le n H)
    have hnt := ht n (t.max'_mem hne)
    have hn0 : 0 ≤ (2 : ℝ)^n*H := by positivity
    nlinarith
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty]
    positivity

end MahlerLean
