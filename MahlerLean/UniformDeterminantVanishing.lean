import MahlerLean.UniformPerturbedDeterminant

open Set
noncomputable section
namespace MahlerLean

/-- Choose the perturbation constant before both the adaptive degree and
source cell, by summing constants over the fixed finite degree range. -/
theorem exists_targetLinearMatrix_uniform_degree_bound
    {f : ℝ → ℝ} {U : Set ℝ} (hf : AnalyticOnNhd ℝ f U)
    (D : ℕ) {a b : ℝ} (hab : a < b) (hI : Icc a b ⊆ U) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ d : ℕ, d ≤ D →
      ∀ c, a ≤ c → c < b → ∀ ρ δ : ℝ,
        0 < ρ → ρ ≤ 1 → 0 ≤ δ → δ ≤ ρ ^ (2 * (d + 1)) →
        ∀ x y : Fin (2 * (d + 1)) → ℝ,
          (∀ i, x i ∈ Icc c b) → (∀ i, x i - c ≤ ρ) →
          (∀ i, |y i - f (x i)| ≤ δ) →
          |(targetLinearMatrix d x y).det| ≤
            K * ρ ^ ((2 * (d + 1)) * (2 * (d + 1) - 1) / 2) := by
  classical
  have hex (d : Fin (D + 1)) :=
    exists_targetLinearMatrix_uniform_perturbed_bound hf d.val hab hI
  choose K hK hbound using hex
  refine ⟨∑ d, K d, Finset.sum_nonneg (fun d _ ↦ hK d), ?_⟩
  intro d hd c hac hcb ρ δ hρ hρ1 hδ hsmall x y hx hxρ herr
  have hb := hbound ⟨d, by omega⟩ c hac hcb ρ δ hρ hρ1 hδ hsmall x y hx hxρ herr
  exact hb.trans (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun j _ ↦ hK j)
      (Finset.mem_univ (⟨d, by omega⟩ : Fin (D + 1)))) (pow_nonneg hρ.le _))

/-- Strong two-height determinant comparison with one constant valid for
all degrees up to D and all cells of the parent interval. The error enters
only through delta ≤ rho^N, without an additive delta term. -/
theorem exists_targetLinearMatrix_det_zero_uniform_cells
    {f : ℝ → ℝ} {U : Set ℝ} (hf : AnalyticOnNhd ℝ f U)
    (D : ℕ) {a b : ℝ} (hab : a < b) (hI : Icc a b ⊆ U) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ d : ℕ, d ≤ D →
      ∀ c, a ≤ c → c < b → ∀ {Q H ρ δ : ℝ}
        (p r : Fin (2 * (d + 1)) → ℤ)
        (q s : Fin (2 * (d + 1)) → ℕ),
        0 < Q → 0 < H →
        (∀ i, 0 < q i) → (∀ i, 0 < s i) →
        (∀ i, (q i : ℝ) ≤ 2 * Q) → (∀ i, (s i : ℝ) ≤ 2 * H) →
        0 < ρ → ρ ≤ 1 → 0 ≤ δ → δ ≤ ρ ^ (2 * (d + 1)) →
        (∀ i, (p i : ℝ) / q i ∈ Icc c b) →
        (∀ i, (p i : ℝ) / q i - c ≤ ρ) →
        (∀ i, |(r i : ℝ) / s i - f ((p i : ℝ) / q i)| ≤ δ) →
        K * ρ ^ ((2 * (d + 1)) * (2 * (d + 1) - 1) / 2) <
          1 / ((2 * Q) ^ (d * (2 * (d + 1))) * (2 * H) ^ (2 * (d + 1))) →
        (targetLinearMatrix d (fun i ↦ (p i : ℝ) / q i)
          (fun i ↦ (r i : ℝ) / s i)).det = 0 := by
  obtain ⟨K, hK, hbound⟩ := exists_targetLinearMatrix_uniform_degree_bound hf D hab hI
  refine ⟨K, hK, ?_⟩
  intro d hd c hac hcb Q H ρ δ p r q s hQ hH hq hs hqQ hsH
    hρ hρ1 hδ hsmall hx hxρ herr hcompare
  apply targetLinearMatrix_det_eq_zero_of_lt d p r q s hq hs hQ hH hqQ hsH
  exact (hbound d hd c hac hcb ρ δ hρ hρ1 hδ hsmall
    (fun i ↦ (p i : ℝ) / q i) (fun i ↦ (r i : ℝ) / s i) hx hxρ herr).trans_lt hcompare

end MahlerLean
