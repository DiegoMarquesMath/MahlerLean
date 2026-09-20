import MahlerLean.DeterminantRowExpansion
import MahlerLean.TargetLinearCurveTaylor

/-!
Uniform determinant decay for a smooth curve.  We deliberately take the
Taylor order at least `N(N-1)/2`: then every term containing a Taylor
remainder has at least the same radius power as the alternating principal
term.  This avoids losing the triangular exponent in the rowwise expansion.
-/

open scoped BigOperators
open Set

noncomputable section
namespace MahlerLean

/-- Matrix obtained by evaluating a vector-valued curve at `N` source points. -/
def curveValueMatrix {N : ℕ} (Φ : ℝ → (Fin N → ℝ))
    (x : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i => Φ (x i)

/-- Matrix of Taylor-polynomial rows of order `S-1`. -/
def curveTaylorMatrix {N : ℕ} (S : ℕ) (Φ : ℝ → (Fin N → ℝ))
    (s : Set ℝ) (a : ℝ) (x : Fin N → ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun i => taylorWithinEval Φ (S - 1) s a (x i)

/-- Rowwise Taylor remainder matrix. -/
def curveTaylorRemainderMatrix {N : ℕ} (S : ℕ)
    (Φ : ℝ → (Fin N → ℝ)) (s : Set ℝ) (a : ℝ)
    (x : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  curveValueMatrix Φ x - curveTaylorMatrix S Φ s a x

theorem curveValueMatrix_eq_taylor_add_remainder {N S : ℕ}
    (Φ : ℝ → (Fin N → ℝ)) (s : Set ℝ) (a : ℝ)
    (x : Fin N → ℝ) :
    curveValueMatrix Φ x = curveTaylorMatrix S Φ s a x +
      curveTaylorRemainderMatrix S Φ s a x := by
  simp [curveTaylorRemainderMatrix]

/-- The row `L¹` size satisfies the triangle inequality for subtraction. -/
theorem matrixRowL1_sub_le {m n : Type*} [Fintype n]
    (A B : Matrix m n ℝ) (i : m) :
    matrixRowL1 (A - B) i ≤ matrixRowL1 A i + matrixRowL1 B i := by
  unfold matrixRowL1
  calc
    (∑ j, |(A - B) i j|) ≤ ∑ j, (|A i j| + |B i j|) := by
      apply Finset.sum_le_sum
      intro j _
      simpa using abs_sub (A i j) (B i j)
    _ = (∑ j, |A i j|) + ∑ j, |B i j| := Finset.sum_add_distrib

/-- A vector norm remainder estimate gives the corresponding row `L¹`
estimate, with the dimension as the only loss. -/
theorem curveTaylorRemainderMatrix_rowL1_le {N S : ℕ}
    (Φ : ℝ → (Fin N → ℝ)) (s : Set ℝ) (a : ℝ)
    (x : Fin N → ℝ) {C ρ : ℝ}
    (hrem : ∀ i, ‖Φ (x i) -
      taylorWithinEval Φ (S - 1) s a (x i)‖ ≤ C * ρ ^ S)
    (i : Fin N) :
    matrixRowL1 (curveTaylorRemainderMatrix S Φ s a x) i ≤
      (N : ℝ) * (C * ρ ^ S) := by
  refine (matrixRowL1_le_card_mul_norm
    (curveTaylorRemainderMatrix S Φ s a x) i).trans ?_
  simpa [curveTaylorRemainderMatrix, curveValueMatrix, curveTaylorMatrix] using
    (mul_le_mul_of_nonneg_left (hrem i) (Nat.cast_nonneg N))

/-- Complete analytic assembly.  The principal Taylor determinant has the
alternating exponent `N(N-1)/2`; taking a Taylor order `S` at least that
large ensures that every mixed remainder term has the same power or better. -/
theorem abs_det_curveValueMatrix_le_of_taylor {N S : ℕ}
    (hS : 0 < S) (htri : N * (N - 1) / 2 ≤ S)
    (Φ : ℝ → (Fin N → ℝ)) (s : Set ℝ) {a b ρ C B : ℝ}
    {x : Fin N → ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hx : ∀ i, x i ∈ Icc a b) (hxρ : ∀ i, x i - a ≤ ρ)
    (hC0 : 0 ≤ C) (hB0 : 0 ≤ B)
    (hrem : ∀ i, ‖Φ (x i) -
      taylorWithinEval Φ (S - 1) s a (x i)‖ ≤ C * ρ ^ S)
    (hP : ∀ i, matrixRowL1 (curveTaylorMatrix S Φ s a x) i ≤ B)
    (hR : ∀ i, matrixRowL1
      (curveTaylorRemainderMatrix S Φ s a x) i ≤ B) :
    |(curveValueMatrix Φ x).det| ≤
      Fintype.card (Fin N → Bool) *
        (Fintype.card (Fin N → Fin S) *
            (ρ ^ (N * (N - 1) / 2) *
              derivativeDeterminantSum
                (fun k : Fin S => iteratedDerivWithin k.val Φ s a)) +
          Fintype.card (Equiv.Perm (Fin N)) *
            (((N : ℝ) * C * ρ ^ (N * (N - 1) / 2)) *
              B ^ (N - 1))) := by
  have hpow : ρ ^ S ≤ ρ ^ (N * (N - 1) / 2) :=
    pow_le_pow_of_le_one hρ0 hρ1 htri
  have hsmall : ∀ i, matrixRowL1
      (curveTaylorRemainderMatrix S Φ s a x) i ≤
        (N : ℝ) * C * ρ ^ (N * (N - 1) / 2) := by
    intro i
    calc
      matrixRowL1 (curveTaylorRemainderMatrix S Φ s a x) i ≤
          (N : ℝ) * (C * ρ ^ S) :=
        curveTaylorRemainderMatrix_rowL1_le Φ s a x hrem i
      _ ≤ (N : ℝ) * (C * ρ ^ (N * (N - 1) / 2)) := by
        gcongr
      _ = (N : ℝ) * C * ρ ^ (N * (N - 1) / 2) := by ring
  have hE0 : 0 ≤ (N : ℝ) * C * ρ ^ (N * (N - 1) / 2) := by positivity
  rw [curveValueMatrix_eq_taylor_add_remainder (S := S) Φ s a x]
  simpa only [Fintype.card_fin] using
    (abs_det_add_le_of_remainder_rows
    (curveTaylorMatrix S Φ s a x)
    (curveTaylorRemainderMatrix S Φ s a x)
    (A := Fintype.card (Fin N → Fin S) *
      (ρ ^ (N * (N - 1) / 2) *
        derivativeDeterminantSum
          (fun k : Fin S => iteratedDerivWithin k.val Φ s a)))
    (E := (N : ℝ) * C * ρ ^ (N * (N - 1) / 2))
    (B := B)
    (abs_det_taylorWithinEval_le hS Φ s hρ0 hρ1 hx hxρ)
    hE0 hB0 hP hR hsmall)

/-- Uniform triangular determinant decay for the target-linear analytic
curve.  All analytic quantities are absorbed into one constant independent
of the radius and of the chosen source points. -/
theorem exists_targetLinearCurve_determinant_bound
    {f : ℝ → ℝ} {U : Set ℝ} (hf : AnalyticOnNhd ℝ f U)
    (d : ℕ) {a b : ℝ} (hab : a ≤ b) (hI : Icc a b ⊆ U) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ρ : ℝ), 0 ≤ ρ → ρ ≤ 1 →
      ∀ x : Fin (2 * (d + 1)) → ℝ,
        (∀ i, x i ∈ Icc a b) → (∀ i, x i - a ≤ ρ) →
        |(targetLinearMatrix d x (fun i => f (x i))).det| ≤
          K * ρ ^ ((2 * (d + 1)) * (2 * (d + 1) - 1) / 2) := by
  let N : ℕ := 2 * (d + 1)
  let T : ℕ := N * (N - 1) / 2
  have hN : 0 < N := by simp [N]
  have hN2 : 2 ≤ N := by simp [N]
  have hT : 0 < T := by
    apply Nat.div_pos
    · have hpred : 1 ≤ N - 1 := by omega
      calc
        2 = 2 * 1 := by omega
        _ ≤ N * (N - 1) := Nat.mul_le_mul hN2 hpred
    · omega
  have horder : T - 1 + 1 = T := Nat.sub_add_cancel hT
  have hcurve : ContDiffOn ℝ (T : WithTop ℕ∞)
      (targetLinearCurve f d) (Icc a b) :=
    targetLinearCurve_contDiffOn hf hI d T
  obtain ⟨C, hC0, hC⟩ :=
    exists_taylor_remainder_bound_on_radius
      (Φ := targetLinearCurve f d) (a := a) (b := b)
      (n := T - 1) hab (by
        convert hcurve using 1
        exact_mod_cast horder)
  have hcont : ContinuousOn (targetLinearCurve f d) (Icc a b) :=
    hcurve.continuousOn
  obtain ⟨L, hL⟩ := bddAbove_def.mp
    (isCompact_Icc.bddAbove_image hcont.norm)
  let L₀ : ℝ := max L 0
  have hL₀0 : 0 ≤ L₀ := le_max_right L 0
  have hnorm : ∀ t ∈ Icc a b, ‖targetLinearCurve f d t‖ ≤ L₀ := by
    intro t ht
    exact (hL _ ⟨t, ht, rfl⟩).trans (le_max_left L 0)
  let B : ℝ := (N : ℝ) * (L₀ + C)
  have hB0 : 0 ≤ B := by
    dsimp [B]
    positivity
  let D : ℝ := derivativeDeterminantSum
    (fun k : Fin T => iteratedDerivWithin k.val
      (targetLinearCurve f d) (Icc a b) a)
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
  have hrem : ∀ i, ‖targetLinearCurve f d (x i) -
      taylorWithinEval (targetLinearCurve f d) (T - 1)
        (Icc a b) a (x i)‖ ≤ C * ρ ^ T := by
    intro i
    simpa [horder] using hC ρ hρ0 (x i) (hx i) (hxρ i)
  have hRone : ∀ i, matrixRowL1
      (curveTaylorRemainderMatrix T (targetLinearCurve f d)
        (Icc a b) a x) i ≤ (N : ℝ) * C := by
    intro i
    calc
      matrixRowL1
          (curveTaylorRemainderMatrix T (targetLinearCurve f d)
            (Icc a b) a x) i ≤ (N : ℝ) * (C * ρ ^ T) := by
        simpa [N] using
          (curveTaylorRemainderMatrix_rowL1_le
            (targetLinearCurve f d) (Icc a b) a x hrem i)
      _ ≤ (N : ℝ) * C := by
        have : C * ρ ^ T ≤ C * 1 :=
          mul_le_mul_of_nonneg_left hρpow hC0
        simpa using mul_le_mul_of_nonneg_left this (Nat.cast_nonneg N)
  have hR : ∀ i, matrixRowL1
      (curveTaylorRemainderMatrix T (targetLinearCurve f d)
        (Icc a b) a x) i ≤ B := by
    intro i
    refine (hRone i).trans ?_
    dsimp [B]
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hL₀0)
      (Nat.cast_nonneg N)
  have hvalue : ∀ i, matrixRowL1
      (curveValueMatrix (targetLinearCurve f d) x) i ≤
        (N : ℝ) * L₀ := by
    intro i
    refine (matrixRowL1_le_card_mul_norm
      (curveValueMatrix (targetLinearCurve f d) x) i).trans ?_
    simpa [curveValueMatrix, N] using
      (mul_le_mul_of_nonneg_left (hnorm (x i) (hx i)) (Nat.cast_nonneg N))
  have hP : ∀ i, matrixRowL1
      (curveTaylorMatrix T (targetLinearCurve f d) (Icc a b) a x) i ≤ B := by
    intro i
    have hmatrix : curveTaylorMatrix T (targetLinearCurve f d)
        (Icc a b) a x =
        curveValueMatrix (targetLinearCurve f d) x -
          curveTaylorRemainderMatrix T (targetLinearCurve f d)
            (Icc a b) a x := by
      simp [curveTaylorRemainderMatrix]
    rw [hmatrix]
    refine (matrixRowL1_sub_le _ _ i).trans ?_
    calc
      matrixRowL1 (curveValueMatrix (targetLinearCurve f d) x) i +
          matrixRowL1
            (curveTaylorRemainderMatrix T (targetLinearCurve f d)
              (Icc a b) a x) i ≤ (N : ℝ) * L₀ + (N : ℝ) * C :=
        add_le_add (hvalue i) (hRone i)
      _ = B := by simp [B, mul_add]
  have hraw := abs_det_curveValueMatrix_le_of_taylor
    (N := N) (S := T) hT (le_rfl)
    (targetLinearCurve f d) (Icc a b)
    hρ0 hρ1 hx hxρ hC0 hB0 hrem hP hR
  have hmatrix : curveValueMatrix (targetLinearCurve f d) x =
      targetLinearMatrix d x (fun i => f (x i)) := by
    ext i j
    rfl
  rw [hmatrix] at hraw
  change |(targetLinearMatrix d x (fun i => f (x i))).det| ≤
    K * ρ ^ T
  dsimp [K, D] at hraw ⊢
  convert hraw using 1
  all_goals ring

end MahlerLean
