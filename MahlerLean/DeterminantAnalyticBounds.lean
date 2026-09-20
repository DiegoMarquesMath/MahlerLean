import MahlerLean.TargetLinearDeterminant
import Mathlib.Tactic.Linarith

/-!
Analytic groundwork for the determinant upper bound.  We use the row
`L¹` size because it interacts directly with the Leibniz formula and
does not require a separately developed norm on exterior powers.
-/

open scoped BigOperators

noncomputable section
namespace MahlerLean

/-- The `L¹` size of a row of a real matrix. -/
def matrixRowL1 {m n : Type*} [Fintype n] (M : Matrix m n ℝ) (i : m) : ℝ :=
  ∑ j, |M i j|

theorem matrix_entry_le_rowL1 {m n : Type*} [Fintype n]
    (M : Matrix m n ℝ) (i : m) (j : n) :
    |M i j| ≤ matrixRowL1 M i := by
  exact Finset.single_le_sum (fun k _ => abs_nonneg (M i k)) (Finset.mem_univ j)

/-- A Leibniz-formula bound for a determinant.  Keeping the sum over
permutations is convenient when different rows have different sizes. -/
theorem abs_det_le_sum_perm_prod_rowL1
    {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℝ) :
    |M.det| ≤ ∑ σ : Equiv.Perm n, ∏ i, matrixRowL1 M (σ i) := by
  rw [Matrix.det_apply]
  calc
    |∑ σ : Equiv.Perm n, Equiv.Perm.sign σ • ∏ i, M (σ i) i| ≤
        ∑ σ : Equiv.Perm n, |Equiv.Perm.sign σ • ∏ i, M (σ i) i| :=
      by
        simpa using Finset.abs_sum_le_sum_abs
          (fun σ : Equiv.Perm n => Equiv.Perm.sign σ • (∏ i, M (σ i) i)) Finset.univ
    _ ≤ ∑ σ : Equiv.Perm n, ∏ i, matrixRowL1 M (σ i) := by
      apply Finset.sum_le_sum
      intro σ _
      rw [Units.smul_def, abs_zsmul, Equiv.Perm.sign_abs, one_zsmul,
        Finset.abs_prod]
      exact Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ =>
        matrix_entry_le_rowL1 M (σ i) i)

/-- A uniform version of the determinant bound when every row has the
same `L¹` bound. -/
theorem abs_det_le_perm_card_mul_pow
    {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℝ)
    {K : ℝ} (hrow : ∀ i, matrixRowL1 M i ≤ K) :
    |M.det| ≤ Fintype.card (Equiv.Perm n) * K ^ Fintype.card n := by
  refine (abs_det_le_sum_perm_prod_rowL1 M).trans ?_
  calc
    ∑ σ : Equiv.Perm n, ∏ i, matrixRowL1 M (σ i) ≤
        ∑ _σ : Equiv.Perm n, ∏ _i : n, K := by
      apply Finset.sum_le_sum
      intro σ _
      exact Finset.prod_le_prod (fun i _ => by
        exact (abs_nonneg _).trans (matrix_entry_le_rowL1 M (σ i) i))
        (fun i _ => hrow (σ i))
    _ = Fintype.card (Equiv.Perm n) * K ^ Fintype.card n := by simp

/-- Difference between a target-linear monomial row at heights `y` and `z`. -/
def targetLinearPerturbation (d : ℕ) (x y z : ℝ) :
    Fin (2 * (d + 1)) → ℝ :=
  fun j => x ^ (j.val / 2) * y ^ (j.val % 2) -
    x ^ (j.val / 2) * z ^ (j.val % 2)

/-- Even coordinates do not change, while odd coordinates change by
`x^i (y-z)`. -/
theorem targetLinearPerturbation_apply (d : ℕ) (x y z : ℝ)
    (j : Fin (2 * (d + 1))) :
    targetLinearPerturbation d x y z j =
      if j.val % 2 = 0 then 0 else x ^ (j.val / 2) * (y - z) := by
  have hj : j.val % 2 = 0 ∨ j.val % 2 = 1 := by omega
  rcases hj with hj | hj
  · simp [targetLinearPerturbation, hj]
  · simp [targetLinearPerturbation, hj, mul_sub]

/-- Uniform coordinate bound for the vertical perturbation. -/
theorem abs_targetLinearPerturbation_le (d : ℕ) {x y z X δ : ℝ}
    (hX : 1 ≤ X) (hx : |x| ≤ X) (hδ : |y - z| ≤ δ)
    (j : Fin (2 * (d + 1))) :
    |targetLinearPerturbation d x y z j| ≤ X ^ d * δ := by
  have hi : j.val / 2 ≤ d := by have := j.isLt; omega
  have hδ0 : 0 ≤ δ := (abs_nonneg (y - z)).trans hδ
  rw [targetLinearPerturbation_apply]
  split_ifs
  · simpa using mul_nonneg (pow_nonneg (le_trans zero_le_one hX) d) hδ0
  · rw [abs_mul, abs_pow]
    calc
      |x| ^ (j.val / 2) * |y - z| ≤ X ^ (j.val / 2) * δ :=
        mul_le_mul (pow_le_pow_left₀ (abs_nonneg x) hx _) hδ
          (abs_nonneg _) (pow_nonneg (le_trans zero_le_one hX) _)
      _ ≤ X ^ d * δ := mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hX hi) hδ0

/-- `L¹` control of the whole perturbation row. -/
theorem targetLinearPerturbation_l1_le (d : ℕ) {x y z X δ : ℝ}
    (hX : 1 ≤ X) (hx : |x| ≤ X) (hδ : |y - z| ≤ δ) :
    (∑ j : Fin (2 * (d + 1)), |targetLinearPerturbation d x y z j|) ≤
      (2 * (d + 1) : ℕ) * (X ^ d * δ) := by
  calc
    _ ≤ ∑ _j : Fin (2 * (d + 1)), X ^ d * δ :=
      Finset.sum_le_sum (fun j _ => abs_targetLinearPerturbation_le d hX hx hδ j)
    _ = _ := by simp

/-- Matrix whose `k`th row is the vertical perturbation at the `k`th
source point. -/
def targetLinearPerturbationMatrix (d : ℕ)
    (x y z : Fin (2 * (d + 1)) → ℝ) :
    Matrix (Fin (2 * (d + 1))) (Fin (2 * (d + 1))) ℝ :=
  fun k j => targetLinearPerturbation d (x k) (y k) (z k) j

/-- Exact decomposition of the evaluation matrix into its graph part and
the vertical perturbation matrix. -/
theorem targetLinearMatrix_eq_add_perturbation (d : ℕ)
    (x y z : Fin (2 * (d + 1)) → ℝ) :
    targetLinearMatrix d x y = targetLinearMatrix d x z +
      targetLinearPerturbationMatrix d x y z := by
  ext k j
  change x k ^ (j.val / 2) * y k ^ (j.val % 2) =
    x k ^ (j.val / 2) * z k ^ (j.val % 2) +
      (x k ^ (j.val / 2) * y k ^ (j.val % 2) -
        x k ^ (j.val / 2) * z k ^ (j.val % 2))
  ring

/-- Uniform `L¹` bound for every row of the perturbation matrix. -/
theorem targetLinearPerturbationMatrix_rowL1_le (d : ℕ)
    {x y z : Fin (2 * (d + 1)) → ℝ} {X δ : ℝ}
    (hX : 1 ≤ X) (hx : ∀ k, |x k| ≤ X)
    (hδ : ∀ k, |y k - z k| ≤ δ) (k : Fin (2 * (d + 1))) :
    matrixRowL1 (targetLinearPerturbationMatrix d x y z) k ≤
      (2 * (d + 1) : ℕ) * (X ^ d * δ) := by
  exact targetLinearPerturbation_l1_le d hX (hx k) (hδ k)

/-- Exact exponent identity behind the stability of the determinant
under `r` vertical perturbation rows. -/
theorem perturbation_exponent_identity (N r : ℝ) :
    r * N + (N - r) * (N - r - 1) / 2 =
      N * (N - 1) / 2 + r * (r + 1) / 2 := by
  ring

/-- Each perturbation term has at least the unperturbed determinant exponent. -/
theorem perturbation_exponent_ge (N r : ℝ) (hr : 0 ≤ r) :
    N * (N - 1) / 2 ≤ r * N + (N - r) * (N - r - 1) / 2 := by
  rw [perturbation_exponent_identity]
  nlinarith

end MahlerLean
