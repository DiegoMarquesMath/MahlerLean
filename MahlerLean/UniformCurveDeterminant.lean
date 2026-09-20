import MahlerLean.SmoothCurveMinorDecay
import MahlerLean.UniformTaylorBase

/-! Determinant decay with constants chosen on the parent interval,
uniformly in the moving left endpoint of a source cell. -/
open scoped BigOperators
open Set
noncomputable section
namespace MahlerLean

theorem exists_moving_base_curve_determinant_bound {N : ℕ} (hN2 : 2 ≤ N)
    (Φ : ℝ → (Fin N → ℝ)) {a b : ℝ} (hab : a < b)
    (hΦ : ∀ n : ℕ, ContDiffOn ℝ n Φ (Icc a b)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ c, a ≤ c → c < b → ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 →
      ∀ x : Fin N → ℝ,
        (∀ i, x i ∈ Icc c b) → (∀ i, x i - c ≤ ρ) →
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
    exists_uniform_taylor_remainder_moving_base
      (Φ := Φ) (a := a) (b := b)
      hab (T - 1) (by
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
  have hex (k : Fin T) := exists_uniform_derivative_bound_right_subinterval
    (Φ := Φ) hab k.val (hΦ k.val)
  choose Ld hLd hder using hex
  let Lder : ℝ := ∑ k, Ld k
  have hLder : 0 ≤ Lder := Finset.sum_nonneg (fun k _ ↦ hLd k)
  let D : ℝ := Fintype.card (Fin N → Fin T) *
    (Fintype.card (Equiv.Perm (Fin N)) * ((N : ℝ) * Lder) ^ N)
  have hDsum : ∀ c, a ≤ c → c < b →
      derivativeDeterminantSum (fun k : Fin T ↦ iteratedDerivWithin k.val Φ (Icc c b) c) ≤ D := by
    intro c hac hcb
    unfold derivativeDeterminantSum
    calc
      _ ≤ ∑ _κ : Fin N → Fin T,
          Fintype.card (Equiv.Perm (Fin N)) * ((N : ℝ) * Lder) ^ N := by
        apply Finset.sum_le_sum
        intro κ _
        have hh : ∀ i : Fin N, matrixRowL1
            (fun i ↦ iteratedDerivWithin (κ i).val Φ (Icc c b) c) i ≤ (N : ℝ) * Lder := by
          intro i
          apply (matrixRowL1_le_card_mul_norm _ i).trans
          simp only [Fintype.card_fin]
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
          exact (hder (κ i) c hac hcb c ⟨le_rfl, hcb.le⟩).trans
            (Finset.single_le_sum (fun k _ ↦ hLd k) (Finset.mem_univ (κ i)))
        simpa only [Fintype.card_fin] using abs_det_le_perm_card_mul_pow _ hh
      _ = D := by simp [D]
  let K : ℝ := Fintype.card (Fin N → Bool) *
    (Fintype.card (Fin N → Fin T) * D +
      Fintype.card (Equiv.Perm (Fin N)) *
        (((N : ℝ) * C) * B ^ (N - 1)))
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hK0 : 0 ≤ K := by
    dsimp [K]
    positivity
  refine ⟨K, hK0, ?_⟩
  intro c hac hcb ρ hρ0 hρ1 x hx hxρ
  have hρpow : ρ ^ T ≤ 1 := pow_le_one₀ hρ0 hρ1
  have hrem : ∀ i, ‖Φ (x i) -
      taylorWithinEval Φ (T - 1)
        (Icc c b) c (x i)‖ ≤ C * ρ ^ T := by
    intro i
    simpa [horder] using hC c hac hcb ρ hρ0 (x i) (hx i) (hxρ i)
  have hRone : ∀ i, matrixRowL1
      (curveTaylorRemainderMatrix T Φ
        (Icc c b) c x) i ≤ (N : ℝ) * C := by
    intro i
    calc
      matrixRowL1
          (curveTaylorRemainderMatrix T Φ
            (Icc c b) c x) i ≤ (N : ℝ) * (C * ρ ^ T) := by
        simpa using
          (curveTaylorRemainderMatrix_rowL1_le
            Φ (Icc c b) c x hrem i)
      _ ≤ (N : ℝ) * C := by
        have : C * ρ ^ T ≤ C * 1 :=
          mul_le_mul_of_nonneg_left hρpow hC0
        simpa using mul_le_mul_of_nonneg_left this (Nat.cast_nonneg N)
  have hR : ∀ i, matrixRowL1
      (curveTaylorRemainderMatrix T Φ
        (Icc c b) c x) i ≤ B := by
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
      (mul_le_mul_of_nonneg_left (hnorm (x i) ⟨hac.trans (hx i).1, (hx i).2⟩) (Nat.cast_nonneg N))
  have hP : ∀ i, matrixRowL1
      (curveTaylorMatrix T Φ (Icc c b) c x) i ≤ B := by
    intro i
    have hmatrix : curveTaylorMatrix T Φ
        (Icc c b) c x =
        curveValueMatrix Φ x -
          curveTaylorRemainderMatrix T Φ
            (Icc c b) c x := by
      simp [curveTaylorRemainderMatrix]
    rw [hmatrix]
    refine (matrixRowL1_sub_le _ _ i).trans ?_
    calc
      matrixRowL1 (curveValueMatrix Φ x) i +
          matrixRowL1
            (curveTaylorRemainderMatrix T Φ
              (Icc c b) c x) i ≤ (N : ℝ) * L₀ + (N : ℝ) * C :=
        add_le_add (hvalue i) (hRone i)
      _ = B := by simp [B, mul_add]
  have hraw := abs_det_curveValueMatrix_le_of_taylor
    (N := N) (S := T) hT (le_rfl)
    Φ (Icc c b)
    hρ0 hρ1 hx hxρ hC0 hB0 hrem hP hR
  change |(curveValueMatrix Φ x).det| ≤ K * ρ ^ T
  calc
    _ ≤ Fintype.card (Fin N → Bool) *
        (Fintype.card (Fin N → Fin T) *
          (ρ ^ T * derivativeDeterminantSum
            (fun k : Fin T ↦ iteratedDerivWithin k.val Φ (Icc c b) c)) +
          Fintype.card (Equiv.Perm (Fin N)) *
            (((N : ℝ) * C * ρ ^ T) * B ^ (N - 1))) := hraw
    _ ≤ Fintype.card (Fin N → Bool) *
        (Fintype.card (Fin N → Fin T) * (ρ ^ T * D) +
          Fintype.card (Equiv.Perm (Fin N)) *
            (((N : ℝ) * C * ρ ^ T) * B ^ (N - 1))) := by
      gcongr
      exact hDsum c hac hcb
    _ = K * ρ ^ T := by dsimp [K]; ring

/-- One constant controls every coordinate minor of m curve rows at a
fixed base point. Coordinate selections need not be injective. -/
theorem exists_moving_base_smooth_curve_minor_bound_of_two_le {N m : ℕ} (hm : 2 ≤ m)
    (Φ : ℝ → (Fin N → ℝ)) {a b : ℝ} (hab : a < b)
    (hΦ : ∀ n : ℕ, ContDiffOn ℝ n Φ (Icc a b)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (cols : Fin m → Fin N) (c : ℝ), a ≤ c → c < b → ∀ (ρ : ℝ),
      0 ≤ ρ → ρ ≤ 1 → ∀ x : Fin m → ℝ,
        (∀ i, x i ∈ Icc c b) → (∀ i, x i - c ≤ ρ) →
        |Matrix.det (fun i j ↦ Φ (x i) (cols j))| ≤
          K * ρ ^ (m * (m - 1) / 2) := by
  classical
  have hex : ∀ cols : Fin m → Fin N, ∃ K : ℝ, 0 ≤ K ∧
      ∀ c : ℝ, a ≤ c → c < b → ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 → ∀ x : Fin m → ℝ,
        (∀ i, x i ∈ Icc c b) → (∀ i, x i - c ≤ ρ) →
        |Matrix.det (fun i j ↦ Φ (x i) (cols j))| ≤
          K * ρ ^ (m * (m - 1) / 2) := by
    intro cols
    apply exists_moving_base_curve_determinant_bound hm (fun t j ↦ Φ t (cols j)) hab
    intro n
    exact contDiffOn_pi.mpr (fun j ↦ (contDiffOn_pi.mp (hΦ n)) (cols j))
  choose K hK hbound using hex
  refine ⟨∑ cols, K cols, Finset.sum_nonneg (fun cols _ ↦ hK cols), ?_⟩
  intro cols c hac hcb ρ hρ hρ1 x hx hxρ
  exact (hbound cols c hac hcb ρ hρ hρ1 x hx hxρ).trans
    (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun c _ ↦ hK c) (Finset.mem_univ cols))
      (pow_nonneg hρ _))

/-- All minor sizes, including zero and one remaining curve vector. -/
theorem exists_moving_base_smooth_curve_minor_bound {N m : ℕ}
    (Φ : ℝ → (Fin N → ℝ)) {a b : ℝ} (hab : a < b)
    (hΦ : ∀ n : ℕ, ContDiffOn ℝ n Φ (Icc a b)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (cols : Fin m → Fin N) (c : ℝ), a ≤ c → c < b → ∀ (ρ : ℝ),
      0 ≤ ρ → ρ ≤ 1 → ∀ x : Fin m → ℝ,
        (∀ i, x i ∈ Icc c b) → (∀ i, x i - c ≤ ρ) →
        |Matrix.det (fun i j ↦ Φ (x i) (cols j))| ≤
          K * ρ ^ (m * (m - 1) / 2) := by
  by_cases hm : 2 ≤ m
  · exact exists_moving_base_smooth_curve_minor_bound_of_two_le hm Φ hab hΦ
  have hm' : m = 0 ∨ m = 1 := by omega
  rcases hm' with rfl | rfl
  · refine ⟨1, zero_le_one, ?_⟩
    intros
    simp
  · obtain ⟨L, hL⟩ := bddAbove_def.mp
      (isCompact_Icc.bddAbove_image (hΦ 0).continuousOn.norm)
    refine ⟨max L 0, le_max_right _ _, ?_⟩
    intro cols c hac hcb ρ hρ hρ1 x hx hxρ
    have hb : ‖Φ (x 0)‖ ≤ max L 0 :=
      (hL _ ⟨x 0, ⟨hac.trans (hx 0).1, (hx 0).2⟩, rfl⟩).trans (le_max_left _ _)
    have he := (norm_le_pi_norm (Φ (x 0)) (cols 0)).trans hb
    simpa [Matrix.det_fin_one, Real.norm_eq_abs] using he

end MahlerLean
