import MahlerLean.MixedDeterminantDecay
import MahlerLean.UniformCurveDeterminant

/-! Strong multilinear perturbation estimates with constants independent
of the source cell endpoint inside a fixed compact parent interval. -/
open scoped BigOperators
noncomputable section
namespace MahlerLean

/-- Uniform control of every mixed term uniformly in the Taylor base. The constant
is independent of rho, delta, points, and the choice of error rows. -/
theorem exists_moving_base_curve_mixed_bound {N : ℕ}
    (Φ : ℝ → (Fin N → ℝ)) {a b B : ℝ} (hab : a < b) (hB : 0 ≤ B)
    (hΦ : ∀ n : ℕ, ContDiffOn ℝ n Φ (Set.Icc a b)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c, a ≤ c → c < b → ∀ (ρ δ : ℝ), 0 ≤ ρ → ρ ≤ 1 → 0 ≤ δ →
      ∀ (x : Fin N → ℝ) (E : Matrix (Fin N) (Fin N) ℝ),
        (∀ i, x i ∈ Set.Icc c b) → (∀ i, x i - c ≤ ρ) →
        (∀ i j, |E i j| ≤ B * δ) → ∀ choice : Fin N → Bool,
        |Matrix.det (fun i ↦ if choice i then E i else Φ (x i))| ≤
          C * δ ^ (Finset.univ.filter (fun i ↦ choice i = true)).card *
            ρ ^ mixedCurveExponent N
              (Finset.univ.filter (fun i ↦ choice i = true)).card := by
  classical
  have hex (m : Fin (N + 1)) :=
    exists_moving_base_smooth_curve_minor_bound (m := m.val) Φ hab hΦ
  choose K hK hminor using hex
  let L : ℝ := ∑ m, K m
  have hL : 0 ≤ L := Finset.sum_nonneg (fun m _ ↦ hK m)
  let C : ℝ := (N.factorial : ℝ) * L * (max 1 B) ^ N
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro c hac hcb ρ δ hρ hρ1 hδ x E hx hxρ hE choice
  let M : Matrix (Fin N) (Fin N) ℝ := fun i ↦ if choice i then E i else Φ (x i)
  let r := (Finset.univ.filter (fun i ↦ choice i = true)).card
  have hr : r ≤ N := by
    simpa [r] using Finset.card_filter_le
      (s := (Finset.univ : Finset (Fin N))) (p := fun i ↦ choice i = true)
  have hcount : (∑ i, if choice i then 1 else 0 : ℕ) = r := by
    simp only [Finset.sum_boole]
    rfl
  have hm : ∀ m : ℕ, m ≤ N → ∀ rows cols : Fin m → Fin N,
      (∀ i, choice (rows i) = false) →
      |(M.submatrix rows cols).det| ≤ L * ρ ^ ((m : ℝ) * (m - 1) / 2) := by
    intro m hm rows cols hg
    have hb := hminor ⟨m, by omega⟩ cols c hac hcb ρ hρ hρ1 (fun i ↦ x (rows i))
      (fun i ↦ hx (rows i)) (fun i ↦ hxρ (rows i))
    dsimp only at hb
    rw [← Real.rpow_natCast, triangular_natCast] at hb
    have heq : M.submatrix rows cols = fun i j ↦ Φ (x (rows i)) (cols j) := by
      ext i j
      simp [M, Matrix.submatrix, hg i]
    rw [heq]
    exact hb.trans (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun k _ ↦ hK k) (Finset.mem_univ (⟨m, by omega⟩ : Fin (N + 1))))
      (Real.rpow_nonneg hρ _))
  have hb := abs_det_le_error_power_of_good_minors M choice hL
    (mul_nonneg hB hδ) hρ (fun i hi j ↦ by simpa [M, hi] using hE i j) hm
  rw [hcount] at hb
  have hexp : (((N - r : ℕ) : ℝ) * ((N - r : ℕ) - 1 : ℝ) / 2) =
      mixedCurveExponent N r := by
    simp only [Nat.cast_sub hr, mixedCurveExponent]
  rw [hexp, mul_pow] at hb
  have hp : B ^ r ≤ (max 1 B) ^ N :=
    (pow_le_pow_left₀ hB (le_max_right _ _) r).trans
      (pow_le_pow_right₀ (le_max_left _ _) hr)
  change |M.det| ≤ C * δ ^ r * ρ ^ mixedCurveExponent N r
  calc
    _ ≤ (N.factorial : ℝ) * L * (B ^ r * δ ^ r) *
        ρ ^ mixedCurveExponent N r := hb
    _ ≤ (N.factorial : ℝ) * L * ((max 1 B) ^ N * δ ^ r) *
        ρ ^ mixedCurveExponent N r := by
      gcongr
    _ = _ := by dsimp [C]; ring

/-- Version of (4.8) uniformly in the Taylor base, now with the mixed analytic
bounds proved rather than assumed. -/
theorem exists_moving_base_curve_perturbed_sum_bound {N : ℕ}
    (Φ : ℝ → (Fin N → ℝ)) {a b B : ℝ} (hab : a < b) (hB : 0 ≤ B)
    (hΦ : ∀ n : ℕ, ContDiffOn ℝ n Φ (Set.Icc a b)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c, a ≤ c → c < b → ∀ (ρ δ : ℝ), 0 ≤ ρ → ρ ≤ 1 → 0 ≤ δ →
      ∀ (x : Fin N → ℝ) (E : Matrix (Fin N) (Fin N) ℝ),
        (∀ i, x i ∈ Set.Icc c b) → (∀ i, x i - c ≤ ρ) →
        (∀ i j, |E i j| ≤ B * δ) →
        |(curveValueMatrix Φ x + E).det| ≤
          C * (∑ r ∈ Finset.range (N + 1), δ ^ r * ρ ^ mixedCurveExponent N r) := by
  obtain ⟨C, hC, hmixed⟩ := exists_moving_base_curve_mixed_bound Φ hab hB hΦ
  refine ⟨Fintype.card (Fin N → Bool) * C, by positivity, ?_⟩
  intro c hac hcb ρ δ hρ hρ1 hδ x E hx hxρ hE
  exact abs_det_add_le_mixed_sum (curveValueMatrix Φ x) E hC hρ hδ
    (hmixed c hac hcb ρ δ hρ hρ1 hδ x E hx hxρ hE)

/-- Strong perturbation corollary with no nonvanishing-Wronskian assumption.
The Taylor base varies throughout the parent interval. -/
theorem exists_moving_base_curve_strong_perturbed_bound {N : ℕ}
    (Φ : ℝ → (Fin N → ℝ)) {a b B : ℝ} (hab : a < b) (hB : 0 ≤ B)
    (hΦ : ∀ n : ℕ, ContDiffOn ℝ n Φ (Set.Icc a b)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ c, a ≤ c → c < b → ∀ (ρ δ : ℝ), 0 < ρ → ρ ≤ 1 → 0 ≤ δ → δ ≤ ρ ^ N →
      ∀ (x : Fin N → ℝ) (E : Matrix (Fin N) (Fin N) ℝ),
        (∀ i, x i ∈ Set.Icc c b) → (∀ i, x i - c ≤ ρ) →
        (∀ i j, |E i j| ≤ B * δ) →
        |(curveValueMatrix Φ x + E).det| ≤ K * ρ ^ (N * (N - 1) / 2) := by
  obtain ⟨C, hC, hsum⟩ := exists_moving_base_curve_perturbed_sum_bound Φ hab hB hΦ
  refine ⟨C * (N + 1), by positivity, ?_⟩
  intro c hac hcb ρ δ hρ hρ1 hδ hsmall x E hx hxρ hE
  have hb := (hsum c hac hcb ρ δ hρ.le hρ1 hδ x E hx hxρ hE).trans
    (mixed_perturbation_sum_le hρ hρ1 hδ hsmall hC)
  rw [← triangular_natCast, Real.rpow_natCast] at hb
  exact hb

/-- Target-linear specialization: replaces the additive perturbation estimate
uniformly over moving cell endpoints in the fixed parent interval. -/
theorem exists_targetLinearMatrix_uniform_perturbed_bound
    {f : ℝ → ℝ} {U : Set ℝ} (hf : AnalyticOnNhd ℝ f U)
    (d : ℕ) {a b : ℝ} (hab : a < b) (hI : Set.Icc a b ⊆ U) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ c, a ≤ c → c < b → ∀ (ρ δ : ℝ), 0 < ρ → ρ ≤ 1 → 0 ≤ δ →
      δ ≤ ρ ^ (2 * (d + 1)) →
      ∀ x y : Fin (2 * (d + 1)) → ℝ,
        (∀ i, x i ∈ Set.Icc c b) → (∀ i, x i - c ≤ ρ) →
        (∀ i, |y i - f (x i)| ≤ δ) →
        |(targetLinearMatrix d x y).det| ≤
          K * ρ ^ ((2 * (d + 1)) * (2 * (d + 1) - 1) / 2) := by
  let X : ℝ := max 1 (max |a| |b|)
  have hX : 1 ≤ X := le_max_left _ _
  have hxX : ∀ z ∈ Set.Icc a b, |z| ≤ X := by
    intro z hz
    have ha : |a| ≤ X := (le_max_left _ _).trans (le_max_right _ _)
    have hb : |b| ≤ X := (le_max_right _ _).trans (le_max_right _ _)
    apply abs_le.mpr
    constructor
    · have := neg_abs_le a
      linarith [hz.1]
    · have := le_abs_self b
      linarith [hz.2]
  obtain ⟨K, hK, hbound⟩ := exists_moving_base_curve_strong_perturbed_bound
    (targetLinearCurve f d) (B := X ^ d) hab
    (pow_nonneg (zero_le_one.trans hX) d)
    (fun n ↦ targetLinearCurve_contDiffOn hf hI d n)
  refine ⟨K, hK, ?_⟩
  intro c hac hcb ρ δ hρ hρ1 hδ hsmall x y hx hxρ herr
  have hb := hbound c hac hcb ρ δ hρ hρ1 hδ hsmall x
    (targetLinearPerturbationMatrix d x y (fun i ↦ f (x i))) hx hxρ
    (fun i j ↦ abs_targetLinearPerturbation_le d hX (hxX (x i) ⟨hac.trans (hx i).1, (hx i).2⟩) (herr i) j)
  rw [targetLinearMatrix_eq_add_perturbation d x y (fun i ↦ f (x i))]
  exact hb

end MahlerLean
