import MahlerLean.AnalyticTaylorInjectivity
import Mathlib.LinearAlgebra.Vandermonde

noncomputable section
namespace MahlerLean

/-- The coefficient matrix of differentiated leading monomials is Vandermonde. -/
theorem det_descFactorial_eq_vandermonde {N : ℕ} (r : Fin N → ℕ) :
    Matrix.det (fun i j : Fin N ↦ ((r j).descFactorial i.val : ℝ)) =
      (Matrix.vandermonde (fun j ↦ (r j : ℝ))).det := by
  have h := Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde
    (fun j : Fin N ↦ (r j : ℝ)) (fun i : Fin N ↦ descPochhammer ℝ i.val)
    (fun i ↦ descPochhammer_natDegree ℝ i.val)
    (fun i ↦ monic_descPochhammer ℝ i.val)
  rw [← Matrix.det_transpose]
  simpa only [Matrix.transpose_apply, Matrix.of_apply,
    descPochhammer_eval_eq_descFactorial] using h.symm

/-- Distinct orders give a nonzero leading determinant. -/
theorem det_descFactorial_ne_zero {N : ℕ} (r : Fin N → ℕ)
    (hr : Function.Injective r) :
    Matrix.det (fun i j : Fin N ↦ ((r j).descFactorial i.val : ℝ)) ≠ 0 := by
  rw [det_descFactorial_eq_vandermonde]
  apply Matrix.det_vandermonde_ne_zero_iff.mpr
  intro i j hij
  apply hr
  exact Nat.cast_injective hij

end MahlerLean
