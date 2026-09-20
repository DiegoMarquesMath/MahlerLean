import MahlerLean.SmoothCurveDeterminantBound

/-!
Joint decay for arbitrary smooth projected curves. Applying this theorem
to a selection of m coordinates of a larger curve controls every m-by-m
minor of its m remaining curve rows, the analytic input needed in the
mixed determinant expansion. Constants here are for a fixed Taylor base.
-/
open scoped BigOperators
open Set
noncomputable section
namespace MahlerLean

/-- Triangular determinant decay for any smooth curve of dimension at least
two, with no target-linear or Wronskian assumption. -/
theorem exists_smooth_curve_determinant_bound {N : ℕ} (hN2 : 2 ≤ N)
    (Φ : ℝ → (Fin N → ℝ)) {a b : ℝ} (hab : a ≤ b)
    (hΦ : ∀ n : ℕ, ContDiffOn ℝ n Φ (Icc a b)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 →
      ∀ x : Fin N → ℝ,
        (∀ i, x i ∈ Icc a b) → (∀ i, x i - a ≤ ρ) →
        |(curveValueMatrix Φ x).det| ≤ K * ρ ^ (N * (N - 1) / 2) := by
  let T : ℕ := N * (N - 1) / 2
  have hT : 0 < T := by
    apply Nat.div_pos
    · have hpred : 1 ≤ N - 1 := by omega
      calc
        2 = 2 * 1 := by omega
        _ ≤ N * (N - 1) := Nat.mul_le_mul hN2 hpred
    · omega
  have horder : T - 1 + 1 = T := Nat.sub_add_cancel hT
  have hcurve : ContDiffOn ℝ (T : WithTop ℕ∞)
      Φ (Icc a b) :=
    hΦ T
  obtain ⟨C, hC0, hC⟩ :=
    exists_taylor_remainder_bound_on_radius
      (Φ := Φ) (a := a) (b := b)
      (n := T - 1) hab (by
        convert hcurve using 1
        exact_mod_cast horder)
  have hcont : ContinuousOn Φ (Icc a b) :=
    hcurve.continuousOn
  obtain ⟨L, hL⟩ := bddAbove_def.mp
    (isCompact_Icc.bddAbove_image hcont.norm)
  let L₀ : ℝ := max L 0
  have hL₀0 : 0 ≤ L₀ := le_max_right L 0
  have hnorm : ∀ t ∈ Icc a b, ‖Φ t‖ ≤ L₀ := by
    intro t ht
    exact (hL _ ⟨t, ht, rfl⟩).trans (le_max_left L 0)
  let B : ℝ := (N : ℝ) * (L₀ + C)
  have hB0 : 0 ≤ B := by
    dsimp [B]
    positivity
  let D : ℝ := derivativeDeterminantSum
    (fun k : Fin T => iteratedDerivWithin k.val
      Φ (Icc a b) a)
  let K : ℝ := Fintype.card (Fin N → Bool) *
    (Fintype.card (Fin N → Fin T) * D +
      Fintype.card (Equiv.Perm (Fin N)) *
        (((N : ℝ) * C) * B ^ (N - 1)))
  have hD0 : 0 ≤ D := derivativeDeterminantSum_nonneg _
  have hK0 : 0 ≤ K := by
    dsimp [K]
    positivity
  refine ⟨K, hK0, ?_⟩
  intro ρ hρ0 hρ1 x hx hxρ
  have hρpow : ρ ^ T ≤ 1 := pow_le_one₀ hρ0 hρ1
  have hrem : ∀ i, ‖Φ (x i) -
      taylorWithinEval Φ (T - 1)
        (Icc a b) a (x i)‖ ≤ C * ρ ^ T := by
    intro i
    simpa [horder] using hC ρ hρ0 (x i) (hx i) (hxρ i)
  have hRone : ∀ i, matrixRowL1
      (curveTaylorRemainderMatrix T Φ
        (Icc a b) a x) i ≤ (N : ℝ) * C := by
    intro i
    calc
      matrixRowL1
          (curveTaylorRemainderMatrix T Φ
            (Icc a b) a x) i ≤ (N : ℝ) * (C * ρ ^ T) := by
        simpa using
          (curveTaylorRemainderMatrix_rowL1_le
            Φ (Icc a b) a x hrem i)
      _ ≤ (N : ℝ) * C := by
        have : C * ρ ^ T ≤ C * 1 :=
          mul_le_mul_of_nonneg_left hρpow hC0
        simpa using mul_le_mul_of_nonneg_left this (Nat.cast_nonneg N)
  have hR : ∀ i, matrixRowL1
      (curveTaylorRemainderMatrix T Φ
        (Icc a b) a x) i ≤ B := by
    intro i
    refine (hRone i).trans ?_
    dsimp [B]
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hL₀0)
      (Nat.cast_nonneg N)
  have hvalue : ∀ i, matrixRowL1
      (curveValueMatrix Φ x) i ≤
        (N : ℝ) * L₀ := by
    intro i
    refine (matrixRowL1_le_card_mul_norm
      (curveValueMatrix Φ x) i).trans ?_
    simpa [curveValueMatrix] using
      (mul_le_mul_of_nonneg_left (hnorm (x i) (hx i)) (Nat.cast_nonneg N))
  have hP : ∀ i, matrixRowL1
      (curveTaylorMatrix T Φ (Icc a b) a x) i ≤ B := by
    intro i
    have hmatrix : curveTaylorMatrix T Φ
        (Icc a b) a x =
        curveValueMatrix Φ x -
          curveTaylorRemainderMatrix T Φ
            (Icc a b) a x := by
      simp [curveTaylorRemainderMatrix]
    rw [hmatrix]
    refine (matrixRowL1_sub_le _ _ i).trans ?_
    calc
      matrixRowL1 (curveValueMatrix Φ x) i +
          matrixRowL1
            (curveTaylorRemainderMatrix T Φ
              (Icc a b) a x) i ≤ (N : ℝ) * L₀ + (N : ℝ) * C :=
        add_le_add (hvalue i) (hRone i)
      _ = B := by simp [B, mul_add]
  have hraw := abs_det_curveValueMatrix_le_of_taylor
    (N := N) (S := T) hT (le_rfl)
    Φ (Icc a b)
    hρ0 hρ1 hx hxρ hC0 hB0 hrem hP hR
  change |(curveValueMatrix Φ x).det| ≤ K * ρ ^ T
  dsimp [K, D] at hraw ⊢
  convert hraw using 1
  all_goals ring

/-- One constant controls every coordinate minor of m curve rows at a
fixed base point. Coordinate selections need not be injective. -/
theorem exists_uniform_smooth_curve_minor_bound_of_two_le {N m : ℕ} (hm : 2 ≤ m)
    (Φ : ℝ → (Fin N → ℝ)) {a b : ℝ} (hab : a ≤ b)
    (hΦ : ∀ n : ℕ, ContDiffOn ℝ n Φ (Icc a b)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (cols : Fin m → Fin N) (ρ : ℝ),
      0 ≤ ρ → ρ ≤ 1 → ∀ x : Fin m → ℝ,
        (∀ i, x i ∈ Icc a b) → (∀ i, x i - a ≤ ρ) →
        |Matrix.det (fun i j ↦ Φ (x i) (cols j))| ≤
          K * ρ ^ (m * (m - 1) / 2) := by
  classical
  have hex : ∀ cols : Fin m → Fin N, ∃ K : ℝ, 0 ≤ K ∧
      ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 → ∀ x : Fin m → ℝ,
        (∀ i, x i ∈ Icc a b) → (∀ i, x i - a ≤ ρ) →
        |Matrix.det (fun i j ↦ Φ (x i) (cols j))| ≤
          K * ρ ^ (m * (m - 1) / 2) := by
    intro cols
    apply exists_smooth_curve_determinant_bound hm (fun t j ↦ Φ t (cols j)) hab
    intro n
    exact contDiffOn_pi.mpr (fun j ↦ (contDiffOn_pi.mp (hΦ n)) (cols j))
  choose K hK hbound using hex
  refine ⟨∑ cols, K cols, Finset.sum_nonneg (fun cols _ ↦ hK cols), ?_⟩
  intro cols ρ hρ hρ1 x hx hxρ
  exact (hbound cols ρ hρ hρ1 x hx hxρ).trans
    (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun c _ ↦ hK c) (Finset.mem_univ cols))
      (pow_nonneg hρ _))

/-- All minor sizes, including zero and one remaining curve vector. -/
theorem exists_uniform_smooth_curve_minor_bound {N m : ℕ}
    (Φ : ℝ → (Fin N → ℝ)) {a b : ℝ} (hab : a ≤ b)
    (hΦ : ∀ n : ℕ, ContDiffOn ℝ n Φ (Icc a b)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (cols : Fin m → Fin N) (ρ : ℝ),
      0 ≤ ρ → ρ ≤ 1 → ∀ x : Fin m → ℝ,
        (∀ i, x i ∈ Icc a b) → (∀ i, x i - a ≤ ρ) →
        |Matrix.det (fun i j ↦ Φ (x i) (cols j))| ≤
          K * ρ ^ (m * (m - 1) / 2) := by
  by_cases hm : 2 ≤ m
  · exact exists_uniform_smooth_curve_minor_bound_of_two_le hm Φ hab hΦ
  have hm' : m = 0 ∨ m = 1 := by omega
  rcases hm' with rfl | rfl
  · refine ⟨1, zero_le_one, ?_⟩
    intros
    simp
  · obtain ⟨L, hL⟩ := bddAbove_def.mp
      (isCompact_Icc.bddAbove_image (hΦ 0).continuousOn.norm)
    refine ⟨max L 0, le_max_right _ _, ?_⟩
    intro cols ρ hρ hρ1 x hx hxρ
    have hb : ‖Φ (x 0)‖ ≤ max L 0 :=
      (hL _ ⟨x 0, hx 0, rfl⟩).trans (le_max_left _ _)
    have he := (norm_le_pi_norm (Φ (x 0)) (cols 0)).trans hb
    simpa [Matrix.det_fin_one, Real.norm_eq_abs] using he

end MahlerLean
