import MahlerLean.MultilinearPerturbation
import MahlerLean.SmoothCurveMinorDecay

open scoped BigOperators
noncomputable section
namespace MahlerLean

theorem triangular_natCast (m : ℕ) :
    ((m * (m - 1) / 2 : ℕ) : ℝ) = (m : ℝ) * (m - 1) / 2 := by
  cases m with
  | zero => norm_num
  | succ n =>
    rw [Nat.cast_div (Nat.even_mul_pred_self (n + 1)).two_dvd (by norm_num)]
    simp only [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ n + 1), Nat.cast_one,
      Nat.cast_ofNat]

/-- Laplace expansion along the error rows retains the joint decay of the
remaining curve minors. Repeated selections of good rows are allowed. -/
theorem abs_det_le_error_power_of_good_minors {N : ℕ}
    (M : Matrix (Fin N) (Fin N) ℝ) (bad : Fin N → Bool)
    {K δ ρ : ℝ} (hK : 0 ≤ K) (hδ : 0 ≤ δ) (hρ : 0 ≤ ρ)
    (herr : ∀ i, bad i = true → ∀ j, |M i j| ≤ δ)
    (hminor : ∀ m : ℕ, m ≤ N → ∀ rows cols : Fin m → Fin N,
      (∀ i, bad (rows i) = false) →
      |(M.submatrix rows cols).det| ≤ K * ρ ^ ((m : ℝ) * (m - 1) / 2)) :
    |M.det| ≤ (N.factorial : ℝ) * K *
      δ ^ (∑ i, if bad i then 1 else 0) *
      ρ ^ (((N - (∑ i, if bad i then 1 else 0) : ℕ) : ℝ) *
        ((N - (∑ i, if bad i then 1 else 0) : ℕ) - 1 : ℝ) / 2) := by
  induction N with
  | zero =>
    simpa using hminor 0 (by omega) id id (by intro i; exact Fin.elim0 i)
  | succ n ih =>
    by_cases hall : ∀ i, bad i = false
    · have hc : (∑ i, if bad i then 1 else 0 : ℕ) = 0 := by simp [hall]
      rw [hc]
      simp only [Nat.sub_zero, pow_zero, mul_one]
      have hb := hminor (n + 1) (by omega) id id hall
      have hf : (1 : ℝ) ≤ (n + 1).factorial := by
        exact_mod_cast Nat.factorial_pos (n + 1)
      exact hb.trans (by
        have hp : 0 ≤ K * ρ ^ (((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) - 1 : ℝ) / 2) :=
          mul_nonneg hK (Real.rpow_nonneg hρ _)
        nlinarith)
    · obtain ⟨i, hi⟩ : ∃ i, bad i = true := by
        push_neg at hall
        obtain ⟨i, hi⟩ := hall
        exact ⟨i, Bool.eq_true_of_not_eq_false hi⟩
      let r : ℕ := ∑ k : Fin n, if bad (i.succAbove k) then 1 else 0
      have hc : (∑ k, if bad k then 1 else 0 : ℕ) = r + 1 := by
        rw [Fin.sum_univ_succAbove _ i]
        simp [hi, r, Nat.add_comm]
      have hrec (j : Fin (n + 1)) :
          |(M.submatrix i.succAbove j.succAbove).det| ≤
            (n.factorial : ℝ) * K * δ ^ r *
              ρ ^ (((n - r : ℕ) : ℝ) * ((n - r : ℕ) - 1 : ℝ) / 2) := by
        apply ih (M.submatrix i.succAbove j.succAbove)
          (fun k ↦ bad (i.succAbove k))
        · intro k hk l
          exact herr _ hk _
        · intro m hm rows cols hg
          exact hminor m (by omega)
            (fun k ↦ i.succAbove (rows k)) (fun k ↦ j.succAbove (cols k)) hg
      rw [hc, Matrix.det_succ_row M i]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc
        _ ≤ ∑ _j : Fin (n + 1), δ * ((n.factorial : ℝ) * K * δ ^ r *
            ρ ^ (((n - r : ℕ) : ℝ) * ((n - r : ℕ) - 1 : ℝ) / 2)) := by
          apply Finset.sum_le_sum
          intro j _
          simp only [abs_mul, abs_neg_one_pow, one_mul]
          exact mul_le_mul (herr i hi j) (hrec j) (abs_nonneg _) hδ
        _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
            Nat.cast_one, pow_succ, Nat.add_sub_add_right]
          ring

/-- Uniform control of every mixed term at a fixed Taylor base. The constant
is independent of rho, delta, points, and the choice of error rows. -/
theorem exists_smooth_curve_mixed_bound {N : ℕ}
    (Φ : ℝ → (Fin N → ℝ)) {a b B : ℝ} (hab : a ≤ b) (hB : 0 ≤ B)
    (hΦ : ∀ n : ℕ, ContDiffOn ℝ n Φ (Set.Icc a b)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ δ : ℝ), 0 ≤ ρ → ρ ≤ 1 → 0 ≤ δ →
      ∀ (x : Fin N → ℝ) (E : Matrix (Fin N) (Fin N) ℝ),
        (∀ i, x i ∈ Set.Icc a b) → (∀ i, x i - a ≤ ρ) →
        (∀ i j, |E i j| ≤ B * δ) → ∀ choice : Fin N → Bool,
        |Matrix.det (fun i ↦ if choice i then E i else Φ (x i))| ≤
          C * δ ^ (Finset.univ.filter (fun i ↦ choice i = true)).card *
            ρ ^ mixedCurveExponent N
              (Finset.univ.filter (fun i ↦ choice i = true)).card := by
  classical
  have hex (m : Fin (N + 1)) :=
    exists_uniform_smooth_curve_minor_bound (m := m.val) Φ hab hΦ
  choose K hK hminor using hex
  let L : ℝ := ∑ m, K m
  have hL : 0 ≤ L := Finset.sum_nonneg (fun m _ ↦ hK m)
  let C : ℝ := (N.factorial : ℝ) * L * (max 1 B) ^ N
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro ρ δ hρ hρ1 hδ x E hx hxρ hE choice
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
    have hb := hminor ⟨m, by omega⟩ cols ρ hρ hρ1 (fun i ↦ x (rows i))
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

/-- Version of (4.8) at a fixed Taylor base, now with the mixed analytic
bounds proved rather than assumed. -/
theorem exists_smooth_curve_perturbed_sum_bound {N : ℕ}
    (Φ : ℝ → (Fin N → ℝ)) {a b B : ℝ} (hab : a ≤ b) (hB : 0 ≤ B)
    (hΦ : ∀ n : ℕ, ContDiffOn ℝ n Φ (Set.Icc a b)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ δ : ℝ), 0 ≤ ρ → ρ ≤ 1 → 0 ≤ δ →
      ∀ (x : Fin N → ℝ) (E : Matrix (Fin N) (Fin N) ℝ),
        (∀ i, x i ∈ Set.Icc a b) → (∀ i, x i - a ≤ ρ) →
        (∀ i j, |E i j| ≤ B * δ) →
        |(curveValueMatrix Φ x + E).det| ≤
          C * (∑ r ∈ Finset.range (N + 1), δ ^ r * ρ ^ mixedCurveExponent N r) := by
  obtain ⟨C, hC, hmixed⟩ := exists_smooth_curve_mixed_bound Φ hab hB hΦ
  refine ⟨Fintype.card (Fin N → Bool) * C, by positivity, ?_⟩
  intro ρ δ hρ hρ1 hδ x E hx hxρ hE
  exact abs_det_add_le_mixed_sum (curveValueMatrix Φ x) E hC hρ hδ
    (hmixed ρ δ hρ hρ1 hδ x E hx hxρ hE)

/-- Strong perturbation corollary with no nonvanishing-Wronskian assumption.
The Taylor base is fixed at the interval's left endpoint. -/
theorem exists_smooth_curve_strong_perturbed_bound {N : ℕ}
    (Φ : ℝ → (Fin N → ℝ)) {a b B : ℝ} (hab : a ≤ b) (hB : 0 ≤ B)
    (hΦ : ∀ n : ℕ, ContDiffOn ℝ n Φ (Set.Icc a b)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ρ δ : ℝ), 0 < ρ → ρ ≤ 1 → 0 ≤ δ → δ ≤ ρ ^ N →
      ∀ (x : Fin N → ℝ) (E : Matrix (Fin N) (Fin N) ℝ),
        (∀ i, x i ∈ Set.Icc a b) → (∀ i, x i - a ≤ ρ) →
        (∀ i j, |E i j| ≤ B * δ) →
        |(curveValueMatrix Φ x + E).det| ≤ K * ρ ^ (N * (N - 1) / 2) := by
  obtain ⟨C, hC, hsum⟩ := exists_smooth_curve_perturbed_sum_bound Φ hab hB hΦ
  refine ⟨C * (N + 1), by positivity, ?_⟩
  intro ρ δ hρ hρ1 hδ hsmall x E hx hxρ hE
  have hb := (hsum ρ δ hρ.le hρ1 hδ x E hx hxρ hE).trans
    (mixed_perturbation_sum_le hρ hρ1 hδ hsmall hC)
  rw [← triangular_natCast, Real.rpow_natCast] at hb
  exact hb

/-- Target-linear specialization: replaces the additive perturbation estimate
for points within rho of the fixed left endpoint. Uniformity over moving
cell endpoints remains a separate step. -/
theorem exists_targetLinearMatrix_strong_perturbed_bound
    {f : ℝ → ℝ} {U : Set ℝ} (hf : AnalyticOnNhd ℝ f U)
    (d : ℕ) {a b : ℝ} (hab : a ≤ b) (hI : Set.Icc a b ⊆ U) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ρ δ : ℝ), 0 < ρ → ρ ≤ 1 → 0 ≤ δ →
      δ ≤ ρ ^ (2 * (d + 1)) →
      ∀ x y : Fin (2 * (d + 1)) → ℝ,
        (∀ i, x i ∈ Set.Icc a b) → (∀ i, x i - a ≤ ρ) →
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
  obtain ⟨K, hK, hbound⟩ := exists_smooth_curve_strong_perturbed_bound
    (targetLinearCurve f d) (B := X ^ d) hab
    (pow_nonneg (zero_le_one.trans hX) d)
    (fun n ↦ targetLinearCurve_contDiffOn hf hI d n)
  refine ⟨K, hK, ?_⟩
  intro ρ δ hρ hρ1 hδ hsmall x y hx hxρ herr
  have hb := hbound ρ δ hρ hρ1 hδ hsmall x
    (targetLinearPerturbationMatrix d x y (fun i ↦ f (x i))) hx hxρ
    (fun i j ↦ abs_targetLinearPerturbation_le d hX (hxX (x i) (hx i)) (herr i) j)
  rw [targetLinearMatrix_eq_add_perturbation d x y (fun i ↦ f (x i))]
  exact hb

end MahlerLean
