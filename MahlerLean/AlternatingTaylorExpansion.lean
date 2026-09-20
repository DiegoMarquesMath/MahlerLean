import MahlerLean.SmoothCurveDeterminant
import Mathlib.Data.Finset.Sort

/-!
Multilinear expansion lemmas for Taylor rows.  The determinant is expanded
over choices of a derivative order in every row; alternation then removes
all repeated choices.
-/

open scoped BigOperators

noncomputable section
namespace MahlerLean

/-- Expand a determinant whose rows are finite linear combinations of a
fixed family of row vectors. -/
theorem det_sum_rows_eq_sum_det
    {n α : Type*} [Fintype n] [DecidableEq n] [Fintype α]
    (c : n → α → ℝ) (v : α → n → ℝ) :
    Matrix.det (fun i => ∑ k, c i k • v k) =
      ∑ κ : n → α, (∏ i, c i (κ i)) * Matrix.det (fun i => v (κ i)) := by
  calc
    Matrix.det (fun i => ∑ k, c i k • v k) =
        ∑ κ : n → α, Matrix.det (fun i => c i (κ i) • v (κ i)) := by
      exact MultilinearMap.map_sum
        (Matrix.detRowAlternating.toMultilinearMap)
        (fun i k => c i k • v k)
    _ = ∑ κ : n → α,
          (∏ i, c i (κ i)) * Matrix.det (fun i => v (κ i)) := by
      apply Finset.sum_congr rfl
      intro κ _
      simpa only [smul_eq_mul] using
        (MultilinearMap.map_smul_univ
          Matrix.detRowAlternating.toMultilinearMap
          (fun i => c i (κ i)) (fun i => v (κ i)))

/-- A non-injective choice of derivative orders contributes zero, because
two rows of the resulting determinant coincide. -/
theorem det_rows_eq_zero_of_not_injective
    {n α : Type*} [Fintype n] [DecidableEq n]
    (v : α → n → ℝ) {κ : n → α} (hκ : ¬ Function.Injective κ) :
    Matrix.det (fun i => v (κ i)) = 0 := by
  rw [Function.not_injective_iff] at hκ
  obtain ⟨i, j, hEq, hij⟩ := hκ
  exact Matrix.det_zero_of_row_eq hij (by simp [hEq])

/-- A strictly increasing sequence of natural numbers indexed by `Fin N`
dominates the identity sequence term by term. -/
theorem fin_val_le_of_strictMono {N : ℕ} (f : Fin N → ℕ)
    (hf : StrictMono f) (i : Fin N) : i.val ≤ f i := by
  cases N with
  | zero => exact Fin.elim0 i
  | succ N =>
      induction i using Fin.inductionOn with
      | zero => exact Nat.zero_le _
      | succ i ih =>
          have hstep : f i.castSucc < f i.succ := hf Fin.lt_succ
          simpa using Nat.succ_le_succ ih |>.trans hstep

/-- Distinct nonnegative derivative orders have sum at least
`0 + ... + (N-1)`. -/
theorem triangular_le_sum_of_injective {N S : ℕ} (κ : Fin N → Fin S)
    (hκ : Function.Injective κ) :
    N * (N - 1) / 2 ≤ ∑ i, (κ i).val := by
  let t : Finset ℕ := Finset.univ.image (fun i : Fin N => (κ i).val)
  have hval : Function.Injective (fun i : Fin N => (κ i).val) := by
    intro i j hij
    apply hκ
    exact Fin.ext hij
  have ht : t.card = N := by
    simp [t, Finset.card_image_of_injective _ hval]
  let e : Fin N ≃o t := t.orderIsoOfFin ht
  calc
    N * (N - 1) / 2 = ∑ i : Fin N, i.val := by
      symm
      rw [Finset.sum_fin_eq_sum_range]
      calc
        (∑ i ∈ Finset.range N, if h : i < N then (⟨i, h⟩ : Fin N).val else 0) =
            ∑ i ∈ Finset.range N, i := by
          apply Finset.sum_congr rfl
          intro i hi
          simp [Finset.mem_range.mp hi]
        _ = N * (N - 1) / 2 := Finset.sum_range_id N
    _ ≤ ∑ i : Fin N, (e i : ℕ) := by
      apply Finset.sum_le_sum
      intro i _
      exact fin_val_le_of_strictMono (fun j => (e j : ℕ)) e.strictMono i
    _ = ∑ z : t, (z : ℕ) := Equiv.sum_comp e.toEquiv (fun z : t => (z : ℕ))
    _ = ∑ z ∈ t, z := Finset.sum_coe_sort t id
    _ = ∑ i : Fin N, (κ i).val := by
      rw [Finset.sum_image hval.injOn]

/-- A Taylor-polynomial determinant has the triangular radius power.  The
constant `D` bounds the finitely many determinants of derivative rows. -/
theorem abs_det_taylor_sum_le {N S : ℕ}
    (v : Fin S → Fin N → ℝ) {a b ρ D : ℝ} {x : Fin N → ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hx : ∀ i, x i ∈ Set.Icc a b) (hxρ : ∀ i, x i - a ≤ ρ)
    (hD0 : 0 ≤ D)
    (hD : ∀ κ : Fin N → Fin S, Function.Injective κ →
      |Matrix.det (fun i => v (κ i))| ≤ D) :
    |Matrix.det (fun i => ∑ k : Fin S,
        (((k.val.factorial : ℝ)⁻¹ * (x i - a) ^ k.val) • v k))| ≤
      Fintype.card (Fin N → Fin S) *
        (ρ ^ (N * (N - 1) / 2) * D) := by
  rw [det_sum_rows_eq_sum_det]
  calc
    |∑ κ : Fin N → Fin S,
        (∏ i, (((κ i).val.factorial : ℝ)⁻¹ *
          (x i - a) ^ (κ i).val)) *
          Matrix.det (fun i => v (κ i))| ≤
        ∑ κ : Fin N → Fin S,
          |(∏ i, (((κ i).val.factorial : ℝ)⁻¹ *
            (x i - a) ^ (κ i).val)) *
            Matrix.det (fun i => v (κ i))| := by
      simpa using Finset.abs_sum_le_sum_abs
        (fun κ : Fin N → Fin S =>
          (∏ i, (((κ i).val.factorial : ℝ)⁻¹ *
            (x i - a) ^ (κ i).val)) *
            Matrix.det (fun i => v (κ i))) Finset.univ
    _ ≤ ∑ _κ : Fin N → Fin S, ρ ^ (N * (N - 1) / 2) * D := by
      apply Finset.sum_le_sum
      intro κ _
      by_cases hκ : Function.Injective κ
      · rw [abs_mul]
        have hcoeff :
            |∏ i, (((κ i).val.factorial : ℝ)⁻¹ *
              (x i - a) ^ (κ i).val)| ≤
              ρ ^ (∑ i, (κ i).val) := by
          rw [Finset.abs_prod, ← Finset.prod_pow_eq_pow_sum]
          apply Finset.prod_le_prod
          · intro i _
            exact abs_nonneg _
          · intro i _
            rw [abs_mul, abs_pow, abs_of_nonneg (sub_nonneg.mpr (hx i).1)]
            have hfac : |((κ i).val.factorial : ℝ)⁻¹| ≤ 1 := by
              rw [abs_inv, abs_of_nonneg (Nat.cast_nonneg _)]
              apply inv_le_one_of_one_le₀
              exact_mod_cast (Nat.factorial_pos (κ i).val)
            calc
              |((κ i).val.factorial : ℝ)⁻¹| * (x i - a) ^ (κ i).val ≤
                  1 * (x i - a) ^ (κ i).val :=
                mul_le_mul_of_nonneg_right hfac
                  (pow_nonneg (sub_nonneg.mpr (hx i).1) _)
              _ ≤ ρ ^ (κ i).val := by
                simpa only [one_mul] using
                  (pow_le_pow_left₀ (sub_nonneg.mpr (hx i).1) (hxρ i) _)
        have hpow : ρ ^ (∑ i, (κ i).val) ≤ ρ ^ (N * (N - 1) / 2) :=
          pow_le_pow_of_le_one hρ0 hρ1 (triangular_le_sum_of_injective κ hκ)
        exact mul_le_mul (hcoeff.trans hpow) (hD κ hκ)
          (abs_nonneg _) (pow_nonneg hρ0 _)
      · rw [det_rows_eq_zero_of_not_injective v hκ, mul_zero, abs_zero]
        exact mul_nonneg (pow_nonneg hρ0 _) hD0
    _ = Fintype.card (Fin N → Fin S) *
          (ρ ^ (N * (N - 1) / 2) * D) := by simp

/-- A canonical finite constant controlling every determinant of derivative
rows up to order `S-1`. -/
def derivativeDeterminantSum {N S : ℕ} (v : Fin S → Fin N → ℝ) : ℝ :=
  ∑ κ : Fin N → Fin S, |Matrix.det (fun i => v (κ i))|

theorem derivativeDeterminantSum_nonneg {N S : ℕ}
    (v : Fin S → Fin N → ℝ) : 0 ≤ derivativeDeterminantSum v := by
  exact Finset.sum_nonneg (fun κ _ => abs_nonneg _)

theorem abs_det_le_derivativeDeterminantSum {N S : ℕ}
    (v : Fin S → Fin N → ℝ) (κ : Fin N → Fin S) :
    |Matrix.det (fun i => v (κ i))| ≤ derivativeDeterminantSum v := by
  unfold derivativeDeterminantSum
  exact Finset.single_le_sum
    (s := Finset.univ)
    (f := fun τ : Fin N → Fin S => |Matrix.det (fun i => v (τ i))|)
    (fun τ _ => abs_nonneg _) (Finset.mem_univ κ)

/-- Actual Taylor-polynomial rows, of any positive order `S`, have the
triangular determinant power dictated only by the number `N` of rows. -/
theorem abs_det_taylorWithinEval_le {N S : ℕ} (hS : 0 < S)
    (Φ : ℝ → (Fin N → ℝ)) (s : Set ℝ) {a b ρ : ℝ}
    {x : Fin N → ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hx : ∀ i, x i ∈ Set.Icc a b) (hxρ : ∀ i, x i - a ≤ ρ) :
    |Matrix.det (fun i => taylorWithinEval Φ (S - 1) s a (x i))| ≤
      Fintype.card (Fin N → Fin S) *
        (ρ ^ (N * (N - 1) / 2) *
          derivativeDeterminantSum
            (fun k : Fin S => iteratedDerivWithin k.val Φ s a)) := by
  have horder : S - 1 + 1 = S :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hS.ne')
  have hrows :
      (fun i => taylorWithinEval Φ (S - 1) s a (x i)) =
        fun i => ∑ k : Fin S,
          (((k.val.factorial : ℝ)⁻¹ * (x i - a) ^ k.val) •
            iteratedDerivWithin k.val Φ s a) := by
    funext i
    rw [taylorWithinEval_eq_derivative_sum, horder,
      ← Fin.sum_univ_eq_sum_range]
  rw [hrows]
  exact abs_det_taylor_sum_le
    (fun k : Fin S => iteratedDerivWithin k.val Φ s a)
    hρ0 hρ1 hx hxρ
    (derivativeDeterminantSum_nonneg _)
    (fun κ _ => abs_det_le_derivativeDeterminantSum
      (v := fun k : Fin S => iteratedDerivWithin k.val Φ s a) κ)

end MahlerLean
