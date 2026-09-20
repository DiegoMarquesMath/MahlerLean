import MahlerLean.CurveTaylorBounds
import MahlerLean.DeterminantAnalyticBounds

/-!
Factorization of a matrix of Taylor-polynomial rows.  This isolates the
Vandermonde powers that later give the exponent `N(N-1)/2`.
-/

open scoped BigOperators
open Set

noncomputable section
namespace MahlerLean

/-- Scalar Taylor coefficients evaluated at the source points. -/
def taylorCoefficientMatrix (N : ℕ) (a : ℝ) (x : Fin N → ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun i k => (((k.val.factorial : ℝ)⁻¹) * (x i - a) ^ k.val)

/-- The matrix whose rows are the derivatives of the curve at the Taylor
base point. -/
def curveDerivativeMatrix {N : ℕ} (Φ : ℝ → (Fin N → ℝ))
    (s : Set ℝ) (a : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun k j => iteratedDerivWithin k.val Φ s a j

/-- The matrix of Taylor-polynomial rows factors into its scalar coefficient
matrix and the matrix of derivative vectors. -/
theorem taylorPolynomialMatrix_eq_mul {N : ℕ} (hN : 0 < N)
    (Φ : ℝ → (Fin N → ℝ))
    (s : Set ℝ) (a : ℝ) (x : Fin N → ℝ) :
    (fun i => taylorWithinEval Φ (N - 1) s a (x i)) =
      taylorCoefficientMatrix N a x * curveDerivativeMatrix Φ s a := by
  ext i j
  rw [taylorWithinEval_eq_derivative_sum]
  have horder : N - 1 + 1 = N := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hN.ne')
  rw [horder]
  rw [← Fin.sum_univ_eq_sum_range]
  simp [Matrix.mul_apply, taylorCoefficientMatrix, curveDerivativeMatrix]

/-- Determinant factorization for the Taylor-polynomial rows. -/
theorem det_taylorPolynomialMatrix_eq_mul {N : ℕ} (hN : 0 < N)
    (Φ : ℝ → (Fin N → ℝ)) (s : Set ℝ) (a : ℝ) (x : Fin N → ℝ) :
    Matrix.det (fun i => taylorWithinEval Φ (N - 1) s a (x i)) =
      (taylorCoefficientMatrix N a x).det *
        (curveDerivativeMatrix Φ s a).det := by
  rw [taylorPolynomialMatrix_eq_mul hN, Matrix.det_mul]

/-- A column of scalar Taylor coefficients has the expected power of the
source radius.  It is stated as a row bound after transposition so that it
feeds directly into the Leibniz determinant estimate. -/
theorem taylorCoefficientMatrix_transpose_rowL1_le {N : ℕ}
    {a b ρ : ℝ} {x : Fin N → ℝ}
    (hx : ∀ i, x i ∈ Icc a b) (hxρ : ∀ i, x i - a ≤ ρ)
    (k : Fin N) :
    matrixRowL1 (taylorCoefficientMatrix N a x).transpose k ≤
      (N : ℝ) * ρ ^ k.val := by
  have hfactorial : |(((k.val.factorial : ℝ)⁻¹))| ≤ 1 := by
    rw [abs_inv, abs_of_nonneg (Nat.cast_nonneg _)]
    apply inv_le_one_of_one_le₀
    exact_mod_cast (Nat.factorial_pos k.val)
  calc
    matrixRowL1 (taylorCoefficientMatrix N a x).transpose k =
        ∑ i : Fin N,
          |(((k.val.factorial : ℝ)⁻¹) * (x i - a) ^ k.val)| := by
      rfl
    _ ≤ ∑ _i : Fin N, ρ ^ k.val := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_pow, abs_of_nonneg (sub_nonneg.mpr (hx i).1)]
      calc
        |(k.val.factorial : ℝ)⁻¹| * (x i - a) ^ k.val ≤
            1 * (x i - a) ^ k.val :=
          mul_le_mul_of_nonneg_right hfactorial (pow_nonneg (sub_nonneg.mpr (hx i).1) _)
        _ ≤ 1 * ρ ^ k.val := by
          simpa only [one_mul] using
            (pow_le_pow_left₀ (sub_nonneg.mpr (hx i).1) (hxρ i) k.val)
        _ = ρ ^ k.val := one_mul _
    _ = (N : ℝ) * ρ ^ k.val := by simp

/-- The scalar Taylor coefficient matrix contributes the triangular power
`ρ^(N(N-1)/2)` to the determinant. -/
theorem abs_det_taylorCoefficientMatrix_le {N : ℕ}
    {a b ρ : ℝ} {x : Fin N → ℝ}
    (hx : ∀ i, x i ∈ Icc a b) (hxρ : ∀ i, x i - a ≤ ρ) :
    |(taylorCoefficientMatrix N a x).det| ≤
      Fintype.card (Equiv.Perm (Fin N)) *
        ((N : ℝ) ^ N * ρ ^ (N * (N - 1) / 2)) := by
  by_cases hN : N = 0
  · subst N
    simp
  have hρ : 0 ≤ ρ := by
    let i : Fin N := ⟨0, Nat.pos_of_ne_zero hN⟩
    exact (sub_nonneg.mpr (hx i).1).trans (hxρ i)
  calc
    |(taylorCoefficientMatrix N a x).det| =
        |(taylorCoefficientMatrix N a x).transpose.det| := by
      rw [Matrix.det_transpose]
    _ ≤ ∑ σ : Equiv.Perm (Fin N),
          ∏ i, matrixRowL1 (taylorCoefficientMatrix N a x).transpose (σ i) :=
      abs_det_le_sum_perm_prod_rowL1 _
    _ ≤ ∑ _σ : Equiv.Perm (Fin N),
          ((N : ℝ) ^ N * ρ ^ (N * (N - 1) / 2)) := by
      apply Finset.sum_le_sum
      intro σ _
      calc
        ∏ i, matrixRowL1 (taylorCoefficientMatrix N a x).transpose (σ i) ≤
            ∏ i, ((N : ℝ) * ρ ^ (σ i).val) := by
          apply Finset.prod_le_prod
          · intro i _
            exact Finset.sum_nonneg (fun j _ => abs_nonneg _)
          · intro i _
            exact taylorCoefficientMatrix_transpose_rowL1_le hx hxρ (σ i)
        _ = ∏ i : Fin N, ((N : ℝ) * ρ ^ i.val) :=
          Equiv.prod_comp σ (fun i : Fin N => (N : ℝ) * ρ ^ i.val)
        _ = (N : ℝ) ^ N * ρ ^ (N * (N - 1) / 2) := by
          rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
          simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          have hsum : (∑ i : Fin N, i.val) = N * (N - 1) / 2 := by
            rw [Finset.sum_fin_eq_sum_range]
            calc
              (∑ i ∈ Finset.range N, if h : i < N then (⟨i, h⟩ : Fin N).val else 0) =
                  ∑ i ∈ Finset.range N, i := by
                apply Finset.sum_congr rfl
                intro i hi
                simp [Finset.mem_range.mp hi]
              _ = N * (N - 1) / 2 := Finset.sum_range_id N
          rw [hsum]
    _ = Fintype.card (Equiv.Perm (Fin N)) *
          ((N : ℝ) ^ N * ρ ^ (N * (N - 1) / 2)) := by simp

/-- Determinant bound for the full matrix of Taylor-polynomial rows.  All
dependence on the derivatives is confined to one fixed determinant. -/
theorem abs_det_taylorPolynomialMatrix_le {N : ℕ} (hN : 0 < N)
    (Φ : ℝ → (Fin N → ℝ)) (s : Set ℝ) {a b ρ : ℝ}
    {x : Fin N → ℝ} (hx : ∀ i, x i ∈ Icc a b)
    (hxρ : ∀ i, x i - a ≤ ρ) :
    |Matrix.det (fun i => taylorWithinEval Φ (N - 1) s a (x i))| ≤
      (Fintype.card (Equiv.Perm (Fin N)) *
          ((N : ℝ) ^ N * ρ ^ (N * (N - 1) / 2))) *
        |(curveDerivativeMatrix Φ s a).det| := by
  rw [det_taylorPolynomialMatrix_eq_mul hN, abs_mul]
  exact mul_le_mul_of_nonneg_right
    (abs_det_taylorCoefficientMatrix_le hx hxρ) (abs_nonneg _)

end MahlerLean
