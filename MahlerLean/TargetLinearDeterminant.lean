import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Arithmetic determinant bounds for the target-linear monomials
`1, y, x, xy, ..., x^d, x^d y`. Source and target denominators are
cleared separately. No reduced-fraction hypothesis is needed.
-/

open scoped BigOperators

noncomputable section
namespace MahlerLean

/-- A nonzero determinant whose rows become integral after positive
scaling is bounded below by the reciprocal of the product of the scales. -/
theorem determinant_lower_bound_of_integral_rows
    {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) (Z : Matrix n n ℤ) (s : n → ℝ)
    (hs : ∀ i, 0 < s i) (hZ : ∀ i j, s i * M i j = (Z i j : ℝ))
    (hdet : M.det ≠ 0) :
    1 / (∏ i, s i) ≤ |M.det| := by
  have hprod : 0 < ∏ i, s i := Finset.prod_pos (fun i _ => hs i)
  have hmatrix : Z.map (fun z => (z : ℝ)) =
      Matrix.of (fun i j => s i * M i j) := by
    ext i j
    exact (hZ i j).symm
  have hcast : (Z.det : ℝ) = (∏ i, s i) * M.det := by
    rw [Int.cast_det, hmatrix, Matrix.det_mul_column]
  have hne : Z.det ≠ 0 := by
    intro hz
    have hzero : (∏ i, s i) * M.det = 0 := by simpa [hz] using hcast.symm
    exact (mul_ne_zero hprod.ne' hdet) hzero
  have hbound : (1 : ℝ) ≤ |(Z.det : ℝ)| := by
    exact_mod_cast Int.one_le_abs hne
  rw [hcast, abs_mul, abs_of_pos hprod] at hbound
  exact (div_le_iff₀ hprod).mpr (by simpa [mul_comm] using hbound)

/-- Evaluation matrix in the same lexicographic order as `rationalFamily`. -/
def targetLinearMatrix (d : ℕ) (x y : Fin (2 * (d + 1)) → ℝ) :
    Matrix (Fin (2 * (d + 1))) (Fin (2 * (d + 1))) ℝ :=
  fun k j => x k ^ (j.val / 2) * y k ^ (j.val % 2)

/-- The integer matrix obtained by multiplying row k by `q_k^d b_k`. -/
def clearedTargetLinearMatrix (d : ℕ)
    (p a : Fin (2 * (d + 1)) → ℤ) (q b : Fin (2 * (d + 1)) → ℕ) :
    Matrix (Fin (2 * (d + 1))) (Fin (2 * (d + 1))) ℤ :=
  fun k j => p k ^ (j.val / 2) * (q k : ℤ) ^ (d - j.val / 2) *
    (if j.val % 2 = 0 then (b k : ℤ) else a k)

/-- Clearing one entry retains degree d in the source denominator and
degree one in the target denominator, also at degree zero. -/
theorem targetLinearMatrix_clear_entry (d : ℕ)
    (p a : Fin (2 * (d + 1)) → ℤ) (q b : Fin (2 * (d + 1)) → ℕ)
    (hq : ∀ k, 0 < q k) (hb : ∀ k, 0 < b k)
    (k j : Fin (2 * (d + 1))) :
    ((q k : ℝ) ^ d * (b k : ℝ)) *
      targetLinearMatrix d (fun k => (p k : ℝ) / q k)
        (fun k => (a k : ℝ) / b k) k j =
      (clearedTargetLinearMatrix d p a q b k j : ℝ) := by
  have hq0 : (q k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hq k))
  have hb0 : (b k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hb k))
  have hi : j.val / 2 ≤ d := by have := j.isLt; omega
  have hpow : (q k : ℝ) ^ d =
      (q k : ℝ) ^ (d - j.val / 2) * (q k : ℝ) ^ (j.val / 2) := by
    rw [← pow_add, Nat.sub_add_cancel hi]
  have hj : j.val % 2 = 0 ∨ j.val % 2 = 1 := by omega
  rcases hj with hj | hj
  · simp only [targetLinearMatrix, clearedTargetLinearMatrix, hj, pow_zero,
      mul_one, if_true, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
    rw [hpow, div_pow]
    field_simp [hq0, hb0]
    <;> ring
  · simp only [targetLinearMatrix, clearedTargetLinearMatrix, hj, pow_one,
      if_neg (by decide : ¬ (1 : ℕ) = 0), Int.cast_mul, Int.cast_pow, Int.cast_natCast]
    rw [hpow, div_pow]
    field_simp [hq0, hb0]
    <;> ring

/-- Exact relation between the rational evaluation determinant and an
integer determinant; no source or target fraction needs to be reduced. -/
theorem targetLinearMatrix_cleared_det (d : ℕ)
    (p a : Fin (2 * (d + 1)) → ℤ) (q b : Fin (2 * (d + 1)) → ℕ)
    (hq : ∀ k, 0 < q k) (hb : ∀ k, 0 < b k) :
    ((clearedTargetLinearMatrix d p a q b).det : ℝ) =
      (∏ k, (q k : ℝ) ^ d * (b k : ℝ)) *
        (targetLinearMatrix d (fun k => (p k : ℝ) / q k)
          (fun k => (a k : ℝ) / b k)).det := by
  rw [Int.cast_det]
  have hm : (clearedTargetLinearMatrix d p a q b).map (fun z => (z : ℝ)) =
      Matrix.of (fun k j => ((q k : ℝ) ^ d * (b k : ℝ)) *
        targetLinearMatrix d (fun k => (p k : ℝ) / q k)
          (fun k => (a k : ℝ) / b k) k j) := by
    ext k j
    exact (targetLinearMatrix_clear_entry d p a q b hq hb k j).symm
  rw [hm, Matrix.det_mul_column]

/-- Arithmetic lower bound in product form (Lemma 4.3 of the manuscript). -/
theorem targetLinearMatrix_det_lower (d : ℕ)
    (p a : Fin (2 * (d + 1)) → ℤ) (q b : Fin (2 * (d + 1)) → ℕ)
    (hq : ∀ k, 0 < q k) (hb : ∀ k, 0 < b k)
    (hdet : (targetLinearMatrix d (fun k => (p k : ℝ) / q k)
      (fun k => (a k : ℝ) / b k)).det ≠ 0) :
    1 / (∏ k, (q k : ℝ) ^ d * (b k : ℝ)) ≤
      |(targetLinearMatrix d (fun k => (p k : ℝ) / q k)
        (fun k => (a k : ℝ) / b k)).det| := by
  apply determinant_lower_bound_of_integral_rows _
    (clearedTargetLinearMatrix d p a q b) (fun k => (q k : ℝ) ^ d * (b k : ℝ)) _ _ hdet
  · intro k
    have hq' : (0 : ℝ) < q k := by exact_mod_cast hq k
    have hb' : (0 : ℝ) < b k := by exact_mod_cast hb k
    positivity
  · exact targetLinearMatrix_clear_entry d p a q b hq hb

/-- The two height scales remain separate in the dyadic lower bound. -/
theorem targetLinearMatrix_det_lower_dyadic (d : ℕ)
    (p a : Fin (2 * (d + 1)) → ℤ) (q b : Fin (2 * (d + 1)) → ℕ)
    (hq : ∀ k, 0 < q k) (hb : ∀ k, 0 < b k)
    {Q B : ℝ} (hQ : 0 < Q) (_hB : 0 < B)
    (hqQ : ∀ k, (q k : ℝ) ≤ 2 * Q) (hbB : ∀ k, (b k : ℝ) ≤ 2 * B)
    (hdet : (targetLinearMatrix d (fun k => (p k : ℝ) / q k)
      (fun k => (a k : ℝ) / b k)).det ≠ 0) :
    1 / ((2 * Q) ^ (d * (2 * (d + 1))) * (2 * B) ^ (2 * (d + 1))) ≤
      |(targetLinearMatrix d (fun k => (p k : ℝ) / q k)
        (fun k => (a k : ℝ) / b k)).det| := by
  have hprod : 0 < ∏ k, (q k : ℝ) ^ d * (b k : ℝ) := by
    apply Finset.prod_pos
    intro k _
    have hq' : (0 : ℝ) < q k := by exact_mod_cast hq k
    have hb' : (0 : ℝ) < b k := by exact_mod_cast hb k
    positivity
  have hupper : (∏ k, (q k : ℝ) ^ d * (b k : ℝ)) ≤
      (2 * Q) ^ (d * (2 * (d + 1))) * (2 * B) ^ (2 * (d + 1)) := by
    calc
      _ ≤ ∏ _k : Fin (2 * (d + 1)), ((2 * Q) ^ d * (2 * B)) := by
        apply Finset.prod_le_prod
        · intro k _; positivity
        · intro k _
          exact mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) (hqQ k) d)
            (hbB k) (Nat.cast_nonneg _) (by positivity)
      _ = _ := by simp [mul_pow, ← pow_mul]
  exact (one_div_le_one_div_of_le hprod hupper).trans
    (targetLinearMatrix_det_lower d p a q b hq hb hdet)

/-- Any strict analytic upper bound below the arithmetic threshold
forces the evaluation determinant to vanish. -/
theorem targetLinearMatrix_det_eq_zero_of_lt (d : ℕ)
    (p a : Fin (2 * (d + 1)) → ℤ) (q b : Fin (2 * (d + 1)) → ℕ)
    (hq : ∀ k, 0 < q k) (hb : ∀ k, 0 < b k)
    {Q B : ℝ} (hQ : 0 < Q) (hB : 0 < B)
    (hqQ : ∀ k, (q k : ℝ) ≤ 2 * Q) (hbB : ∀ k, (b k : ℝ) ≤ 2 * B)
    (hsmall : |(targetLinearMatrix d (fun k => (p k : ℝ) / q k)
      (fun k => (a k : ℝ) / b k)).det| <
      1 / ((2 * Q) ^ (d * (2 * (d + 1))) * (2 * B) ^ (2 * (d + 1)))) :
    (targetLinearMatrix d (fun k => (p k : ℝ) / q k)
      (fun k => (a k : ℝ) / b k)).det = 0 := by
  by_contra hne
  exact (not_lt_of_ge
    (targetLinearMatrix_det_lower_dyadic d p a q b hq hb hQ hB hqQ hbB hne)) hsmall

end MahlerLean
