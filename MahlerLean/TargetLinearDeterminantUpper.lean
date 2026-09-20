import MahlerLean.SmoothCurveDeterminantBound

/-!
Combine the smooth graph determinant estimate with simultaneous vertical
errors.  This is the analytic upper-bound interface used against the
two-height arithmetic lower bound.
-/

open Set

noncomputable section
namespace MahlerLean

/-- Stability of the target-linear determinant under simultaneous vertical
errors.  The graph determinant is controlled by `A`; every perturbed row has
`L¹` size at most `E = N X^d δ`. -/
theorem abs_det_targetLinearMatrix_le_graph_add_error (d : ℕ)
    {x y z : Fin (2 * (d + 1)) → ℝ} {X δ A B : ℝ}
    (hX : 1 ≤ X) (hx : ∀ i, |x i| ≤ X)
    (hδ0 : 0 ≤ δ) (hδ : ∀ i, |y i - z i| ≤ δ)
    (hA : |(targetLinearMatrix d x z).det| ≤ A)
    (hB0 : 0 ≤ B)
    (hgraph : ∀ i, matrixRowL1 (targetLinearMatrix d x z) i ≤ B)
    (herrorB : ((2 * (d + 1) : ℕ) : ℝ) * (X ^ d * δ) ≤ B) :
    |(targetLinearMatrix d x y).det| ≤
      Fintype.card (Fin (2 * (d + 1)) → Bool) *
        (A + Fintype.card (Equiv.Perm (Fin (2 * (d + 1)))) *
          ((((2 * (d + 1) : ℕ) : ℝ) * (X ^ d * δ)) *
            B ^ (2 * (d + 1) - 1))) := by
  have hE0 : 0 ≤ ((2 * (d + 1) : ℕ) : ℝ) * (X ^ d * δ) := by
    positivity
  have hpert : ∀ i, matrixRowL1
      (targetLinearPerturbationMatrix d x y z) i ≤
        ((2 * (d + 1) : ℕ) : ℝ) * (X ^ d * δ) := by
    intro i
    exact targetLinearPerturbationMatrix_rowL1_le d hX hx hδ i
  rw [targetLinearMatrix_eq_add_perturbation d x y z]
  simpa only [Fintype.card_fin] using
    (abs_det_add_le_of_remainder_rows
      (targetLinearMatrix d x z)
      (targetLinearPerturbationMatrix d x y z)
      (A := A)
      (E := ((2 * (d + 1) : ℕ) : ℝ) * (X ^ d * δ))
      (B := B)
      hA hE0 hB0 hgraph
      (fun i => (hpert i).trans herrorB) hpert)

/-- On a compact source interval, the target-linear graph rows have one
uniform `L¹` bound. -/
theorem exists_targetLinearCurve_rowL1_bound
    {f : ℝ → ℝ} {U : Set ℝ} (hf : AnalyticOnNhd ℝ f U)
    (d : ℕ) {a b : ℝ} (hI : Icc a b ⊆ U) :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ t ∈ Icc a b,
      (∑ j : Fin (2 * (d + 1)), |targetLinearCurve f d t j|) ≤ G := by
  have hcont : ContinuousOn (targetLinearCurve f d) (Icc a b) :=
    (targetLinearCurve_contDiffOn hf hI d 0).continuousOn
  obtain ⟨L, hL⟩ := bddAbove_def.mp
    (isCompact_Icc.bddAbove_image hcont.norm)
  let L₀ : ℝ := max L 0
  let G : ℝ := ((2 * (d + 1) : ℕ) : ℝ) * L₀
  have hL₀0 : 0 ≤ L₀ := le_max_right L 0
  refine ⟨G, by
    dsimp [G]
    positivity, ?_⟩
  intro t ht
  have hnorm : ‖targetLinearCurve f d t‖ ≤ L₀ :=
    (hL _ ⟨t, ht, rfl⟩).trans (le_max_left L 0)
  calc
    (∑ j : Fin (2 * (d + 1)), |targetLinearCurve f d t j|) ≤
        Fintype.card (Fin (2 * (d + 1))) •
          ‖targetLinearCurve f d t‖ :=
      Pi.sum_norm_apply_le_norm (ι := Fin (2 * (d + 1)))
        (G := fun _ => ℝ) (targetLinearCurve f d t)
    _ ≤ G := by
      simpa [G, nsmul_eq_mul] using
        (mul_le_mul_of_nonneg_left hnorm
          (Nat.cast_nonneg (2 * (d + 1))))

/-- The complete analytic upper bound for rational points lying vertically
near an analytic graph and horizontally in a source cluster. -/
theorem exists_targetLinearMatrix_analytic_upper_bound
    {f : ℝ → ℝ} {U : Set ℝ} (hf : AnalyticOnNhd ℝ f U)
    (d : ℕ) {a b : ℝ} (hab : a ≤ b) (hI : Icc a b ⊆ U) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (ρ δ : ℝ), 0 ≤ ρ → ρ ≤ 1 → 0 ≤ δ → δ ≤ 1 →
      ∀ (x y : Fin (2 * (d + 1)) → ℝ),
        (∀ i, x i ∈ Icc a b) → (∀ i, x i - a ≤ ρ) →
        (∀ i, |y i - f (x i)| ≤ δ) →
        |(targetLinearMatrix d x y).det| ≤
          K * (ρ ^ ((2 * (d + 1)) * (2 * (d + 1) - 1) / 2) + δ) := by
  let N : ℕ := 2 * (d + 1)
  let T : ℕ := N * (N - 1) / 2
  obtain ⟨Kgraph, hKgraph0, hKgraph⟩ :=
    exists_targetLinearCurve_determinant_bound hf d hab hI
  obtain ⟨G, hG0, hG⟩ :=
    exists_targetLinearCurve_rowL1_bound hf d hI
  let X : ℝ := max 1 (max |a| |b|)
  have hX : 1 ≤ X := le_max_left _ _
  have hX0 : 0 ≤ X := zero_le_one.trans hX
  let E₀ : ℝ := (N : ℝ) * X ^ d
  have hE₀0 : 0 ≤ E₀ := by
    dsimp [E₀]
    positivity
  let B : ℝ := G + E₀
  have hB0 : 0 ≤ B := add_nonneg hG0 hE₀0
  let A₂ : ℝ := Fintype.card (Equiv.Perm (Fin N)) *
    (E₀ * B ^ (N - 1))
  have hA₂0 : 0 ≤ A₂ := by
    dsimp [A₂]
    positivity
  let K : ℝ := Fintype.card (Fin N → Bool) * (Kgraph + A₂)
  have hK0 : 0 ≤ K := by
    dsimp [K]
    positivity
  refine ⟨K, hK0, ?_⟩
  intro ρ δ hρ0 hρ1 hδ0 hδ1 x y hx hxρ herr
  have hxX : ∀ i, |x i| ≤ X := by
    intro i
    exact (abs_le_max_abs_abs (hx i).1 (hx i).2).trans
      (le_max_right 1 (max |a| |b|))
  have hgraphRow : ∀ i,
      matrixRowL1 (targetLinearMatrix d x (fun i => f (x i))) i ≤ B := by
    intro i
    refine (hG (x i) (hx i)).trans ?_
    exact le_add_of_nonneg_right hE₀0
  have herrorB : ((2 * (d + 1) : ℕ) : ℝ) * (X ^ d * δ) ≤ B := by
    calc
      ((2 * (d + 1) : ℕ) : ℝ) * (X ^ d * δ) = E₀ * δ := by
        simp [E₀, N]
        ring
      _ ≤ E₀ * 1 := mul_le_mul_of_nonneg_left hδ1 hE₀0
      _ ≤ B := by
        simpa [B] using (show E₀ ≤ G + E₀ by linarith)
  have hgraphDet :
      |(targetLinearMatrix d x (fun i => f (x i))).det| ≤
        Kgraph * ρ ^ T := by
    simpa [N, T] using hKgraph ρ hρ0 hρ1 x hx hxρ
  have hraw := abs_det_targetLinearMatrix_le_graph_add_error d
    (x := x) (y := y) (z := fun i => f (x i))
    (X := X) (δ := δ) (A := Kgraph * ρ ^ T) (B := B)
    hX hxX hδ0 herr hgraphDet hB0 hgraphRow herrorB
  have hρT0 : 0 ≤ ρ ^ T := pow_nonneg hρ0 T
  have hinner : Kgraph * ρ ^ T + A₂ * δ ≤
      (Kgraph + A₂) * (ρ ^ T + δ) := by
    nlinarith [mul_nonneg hKgraph0 hδ0, mul_nonneg hA₂0 hρT0]
  calc
    |(targetLinearMatrix d x y).det| ≤
        Fintype.card (Fin N → Bool) *
          (Kgraph * ρ ^ T + A₂ * δ) := by
      dsimp [N, T, E₀, A₂] at hraw ⊢
      convert hraw using 1
      all_goals ring
    _ ≤ Fintype.card (Fin N → Bool) *
          ((Kgraph + A₂) * (ρ ^ T + δ)) :=
      mul_le_mul_of_nonneg_left hinner (Nat.cast_nonneg _)
    _ = K * (ρ ^ T + δ) := by simp [K, mul_assoc]
    _ = K *
        (ρ ^ ((2 * (d + 1)) * (2 * (d + 1) - 1) / 2) + δ) := by
      simp [T, N]

end MahlerLean
