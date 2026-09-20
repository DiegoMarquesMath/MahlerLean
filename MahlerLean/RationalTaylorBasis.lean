import MahlerLean.OrderedTaylorBasis

noncomputable section
namespace MahlerLean
open Module

theorem iteratedDeriv_analytic_sum
    {N : ℕ} (φ : Fin N → ℝ → ℝ) (c : Fin N → ℝ)
    {U : Set ℝ} (hφ : ∀ j, AnalyticOnNhd ℝ (φ j) U)
    {x : ℝ} (hx : x ∈ U) (k : ℕ) :
    iteratedDeriv k (fun y ↦ ∑ j, c j * φ j y) x =
      ∑ j, c j * iteratedDeriv k (φ j) x := by
  classical
  have hsum :
      ∀ s : Finset (Fin N),
        iteratedDeriv k
            (fun y => ∑ j ∈ s, c j * φ j y) x
          =
        ∑ j ∈ s,
          c j * iteratedDeriv k (φ j) x := by
    intro s
    induction s using Finset.induction_on with

    | empty =>
        have hkSmooth :
            ContDiffAt ℝ k (fun _ : ℝ => (1 : ℝ)) x :=
          contDiffAt_const

        have hz :=
          iteratedDeriv_const_mul
            (x := x) hkSmooth (0 : ℝ)

        simpa using hz

    | @insert j s hj ih =>
        have hjSmooth :
            ContDiffAt ℝ k (φ j) x :=
          (hφ j x hx).contDiffAt (n := k)

        have hsSmooth :
            ContDiffAt ℝ k
              (fun y => ∑ i ∈ s, c i * φ i y) x := by
          refine ContDiffAt.sum
            (s := s)
            (f := fun i y => c i * φ i y) ?_
          intro i hi
          exact
            contDiffAt_const.mul
              ((hφ i x hx).contDiffAt (n := k))

        have hadd :
            iteratedDeriv k
                (fun y =>
                  c j * φ j y +
                    ∑ i ∈ s, c i * φ i y) x
              =
            iteratedDeriv k
                (fun y => c j * φ j y) x
              +
            iteratedDeriv k
                (fun y => ∑ i ∈ s, c i * φ i y) x := by
          simpa only [Pi.add_apply] using
            (iteratedDeriv_add
              (f := fun y => c j * φ j y)
              (g := fun y => ∑ i ∈ s, c i * φ i y)
              (contDiffAt_const.mul hjSmooth)
              hsSmooth)

        calc
          iteratedDeriv k
              (fun y =>
                ∑ i ∈ insert j s, c i * φ i y) x
              =
            iteratedDeriv k
              (fun y =>
                c j * φ j y +
                  ∑ i ∈ s, c i * φ i y) x := by
                apply congrArg
                  (fun F : ℝ → ℝ =>
                    iteratedDeriv k F x)
                funext y
                rw [Finset.sum_insert hj]

          _ =
            iteratedDeriv k
                (fun y => c j * φ j y) x
              +
            iteratedDeriv k
                (fun y => ∑ i ∈ s, c i * φ i y) x :=
              hadd

          _ =
            c j * iteratedDeriv k (φ j) x
              +
            ∑ i ∈ s,
              c i * iteratedDeriv k (φ i) x := by
                rw [iteratedDeriv_const_mul hjSmooth (c j)]
                rw [ih]

          _ =
            ∑ i ∈ insert j s,
              c i * iteratedDeriv k (φ i) x := by
                rw [Finset.sum_insert hj]

  simpa using hsum Finset.univ

/-- The k-th derivative of a combination, as a linear form on its coefficients. -/
def derivativeCoordinate {N : ℕ} (φ : Fin N → ℝ → ℝ) (z : ℝ) (k : ℕ) :
    (Fin N → ℝ) →ₗ[ℝ] ℝ where
  toFun c := ∑ j, c j * iteratedDeriv k (φ j) z
  map_add' c e := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' t c := by simp [Finset.mul_sum, mul_assoc]

/-- A constant basis change gives rational-family combinations of distinct Taylor orders. -/
theorem rationalFamily_exists_basis_distinct_orders
    {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (hne : U.Nonempty)
    (hconn : IsPreconnected U) (hf : AnalyticOnNhd ℝ f U)
    (hnr : ¬ IsRationalOn f U) (d : ℕ) {z : ℝ} (hz : z ∈ U) :
    ∃ b : Basis (Fin (2 * (d + 1))) ℝ (Fin (2 * (d + 1)) → ℝ),
      ∃ r : Fin (2 * (d + 1)) → ℕ, Function.Injective r ∧
        ∀ i, iteratedDeriv (r i) (fun x ↦ ∑ j, b i j * rationalFamily f d j x) z ≠ 0 ∧
          ∀ k < r i, iteratedDeriv k (fun x ↦ ∑ j, b i j * rationalFamily f d j x) z = 0 := by
  have hsep : ∀ c, (∀ k, derivativeCoordinate (rationalFamily f d) z k c = 0) → c = 0 := by
    intro c hc
    by_contra hcn
    have hn : ∃ j, c j ≠ 0 := by
      by_contra h
      push_neg at h
      exact hcn (funext h)
    obtain ⟨k, hk⟩ := rationalFamily_exists_nonzero_derivative hU hne hconn hf hnr d c hn hz
    apply hk
    rw [iteratedDeriv_analytic_sum _ _ (rationalFamily_analytic hf d) hz]
    exact hc k
  obtain ⟨b, r, hr, hb⟩ := exists_basis_distinct_orders (2 * (d + 1))
    (Fin (2 * (d + 1)) → ℝ) (by simp) (derivativeCoordinate (rationalFamily f d) z) hsep
  refine ⟨b, r, hr, ?_⟩
  intro i
  constructor
  · rw [iteratedDeriv_analytic_sum _ _ (rationalFamily_analytic hf d) hz]
    exact (hb i).1
  · intro k hk
    rw [iteratedDeriv_analytic_sum _ _ (rationalFamily_analytic hf d) hz]
    exact (hb i).2 k hk

/-- A constant coefficient change multiplies the Wronskian by its determinant. -/
theorem wronskian_linearCombination_matrix
    {N : ℕ} (φ : Fin N → ℝ → ℝ) (C : Matrix (Fin N) (Fin N) ℝ)
    {U : Set ℝ} (hφ : ∀ j, AnalyticOnNhd ℝ (φ j) U) {z : ℝ} (hz : z ∈ U) :
    wronskian (fun i x ↦ ∑ j, C i j * φ j x) z = wronskian φ z * C.det := by
  unfold wronskian
  have hmatrix : (fun k i : Fin N ↦ iteratedDeriv k.val (fun x ↦ ∑ j, C i j * φ j x) z) =
      (Matrix.of (fun k j : Fin N ↦ iteratedDeriv k.val (φ j) z)) * C.transpose := by
    funext k i
    rw [iteratedDeriv_analytic_sum _ _ hφ hz]
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  rw [hmatrix, Matrix.det_mul, Matrix.det_transpose]
  rfl

/-- Nonvanishing is preserved by a constant change of coefficient basis. -/
theorem wronskian_basis_ne_zero_iff
    {N : ℕ} (φ : Fin N → ℝ → ℝ) (b : Basis (Fin N) ℝ (Fin N → ℝ))
    {U : Set ℝ} (hφ : ∀ j, AnalyticOnNhd ℝ (φ j) U) {z : ℝ} (hz : z ∈ U) :
    wronskian (fun i x ↦ ∑ j, b i j * φ j x) z ≠ 0 ↔ wronskian φ z ≠ 0 := by
  let C : Matrix (Fin N) (Fin N) ℝ := fun i j ↦ b i j
  have hunit : IsUnit C :=
    Matrix.linearIndependent_rows_iff_isUnit.mp b.linearIndependent
  have hdet : C.det ≠ 0 := (hunit.map (Matrix.detMonoidHom)).ne_zero
  rw [wronskian_linearCombination_matrix φ (fun i j ↦ b i j) hφ hz]
  exact mul_ne_zero_iff.trans (and_iff_left hdet)

end MahlerLean
