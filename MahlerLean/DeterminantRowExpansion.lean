import MahlerLean.AlternatingTaylorExpansion

/-!
Rowwise expansion and a uniform bound for a matrix plus a remainder matrix.
-/

open scoped BigOperators

noncomputable section
namespace MahlerLean

/-- Multilinear expansion of `det (P + R)`, choosing independently in every
row between the principal row and the remainder row. -/
theorem det_add_rows_eq_sum_bool
    {n : Type*} [Fintype n] [DecidableEq n]
    (P R : Matrix n n ℝ) :
    (P + R).det =
      ∑ choice : n → Bool,
        Matrix.det (fun i => if choice i then R i else P i) := by
  change Matrix.detRowAlternating (fun i => P i + R i) = _
  let g : n → Bool → (n → ℝ) := fun i b => if b then R i else P i
  have hsum : (fun i => P i + R i) = fun i => ∑ b : Bool, g i b := by
    funext i
    simp [g, add_comm]
  rw [hsum]
  exact MultilinearMap.map_sum Matrix.detRowAlternating.toMultilinearMap g

/-- If every remainder row is small and all principal and remainder rows are
uniformly bounded, rowwise multilinearity gives a stable determinant bound.
The deliberately harmless factor `2^#n` keeps the statement simple. -/
theorem abs_det_add_le_of_remainder_rows
    {n : Type*} [Fintype n] [DecidableEq n]
    (P R : Matrix n n ℝ) {A E B : ℝ}
    (hA : |P.det| ≤ A) (hE0 : 0 ≤ E) (hB0 : 0 ≤ B)
    (hP : ∀ i, matrixRowL1 P i ≤ B)
    (hR : ∀ i, matrixRowL1 R i ≤ B)
    (hsmall : ∀ i, matrixRowL1 R i ≤ E) :
    |(P + R).det| ≤
      Fintype.card (n → Bool) *
        (A + Fintype.card (Equiv.Perm n) *
          (E * B ^ (Fintype.card n - 1))) := by
  have hA0 : 0 ≤ A := (abs_nonneg P.det).trans hA
  rw [det_add_rows_eq_sum_bool]
  calc
    |∑ choice : n → Bool,
        Matrix.det (fun i => if choice i then R i else P i)| ≤
        ∑ choice : n → Bool,
          |Matrix.det (fun i => if choice i then R i else P i)| := by
      simpa using Finset.abs_sum_le_sum_abs
        (fun choice : n → Bool =>
          Matrix.det (fun i => if choice i then R i else P i)) Finset.univ
    _ ≤ ∑ _choice : n → Bool,
          (A + Fintype.card (Equiv.Perm n) *
            (E * B ^ (Fintype.card n - 1))) := by
      apply Finset.sum_le_sum
      intro choice _
      by_cases hall : ∀ i, choice i = false
      · have hmatrix : (fun i => if choice i then R i else P i) = P := by
          funext i j
          simp [hall i]
        rw [hmatrix]
        exact hA.trans (le_add_of_nonneg_right <|
          mul_nonneg (Nat.cast_nonneg _) <|
            mul_nonneg hE0 (pow_nonneg hB0 _))
      · push_neg at hall
        obtain ⟨i, hi⟩ := hall
        have hitrue : choice i = true := by
          cases h : choice i <;> simp_all
        let M : Matrix n n ℝ := fun j => if choice j then R j else P j
        have hMi : matrixRowL1 M i ≤ E := by
          simpa [M, matrixRowL1, hitrue] using hsmall i
        have hM : ∀ j, matrixRowL1 M j ≤ B := by
          intro j
          by_cases hj : choice j = true
          · simpa [M, matrixRowL1, hj] using hR j
          · have hjfalse : choice j = false := by
              cases h : choice j <;> simp_all
            simpa [M, matrixRowL1, hjfalse] using hP j
        have hdet : |M.det| ≤ Fintype.card (Equiv.Perm n) *
            (E * B ^ (Fintype.card n - 1)) :=
          abs_det_le_perm_card_mul_one_row M i hMi hM
        exact hdet.trans (le_add_of_nonneg_left hA0)
    _ = Fintype.card (n → Bool) *
          (A + Fintype.card (Equiv.Perm n) *
            (E * B ^ (Fintype.card n - 1))) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end MahlerLean
