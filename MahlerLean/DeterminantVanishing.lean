import MahlerLean.TargetLinearDeterminantUpper

/-!
Comparison of the analytic determinant upper bound with the arithmetic
two-height lower bound.  Once the analytic error lies below the reciprocal
denominator threshold, the target-linear determinant must vanish.
-/

open Set

noncomputable section
namespace MahlerLean

/-- Uniform determinant vanishing for clustered rational source points whose
rational target values approximate an analytic graph.  The source height `Q`
and target height `H` remain independent. -/
theorem exists_targetLinearMatrix_det_zero_of_clustered_approximations
    {f : ℝ → ℝ} {U : Set ℝ} (hf : AnalyticOnNhd ℝ f U)
    (d : ℕ) {α β : ℝ} (hαβ : α ≤ β) (hI : Icc α β ⊆ U) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {Q H ρ δ : ℝ}
        (p r : Fin (2 * (d + 1)) → ℤ)
        (q s : Fin (2 * (d + 1)) → ℕ),
        0 < Q → 0 < H →
        (∀ i, 0 < q i) → (∀ i, 0 < s i) →
        (∀ i, (q i : ℝ) ≤ 2 * Q) →
        (∀ i, (s i : ℝ) ≤ 2 * H) →
        0 ≤ ρ → ρ ≤ 1 → 0 ≤ δ → δ ≤ 1 →
        (∀ i, (p i : ℝ) / q i ∈ Icc α β) →
        (∀ i, (p i : ℝ) / q i - α ≤ ρ) →
        (∀ i, |(r i : ℝ) / s i - f ((p i : ℝ) / q i)| ≤ δ) →
        K *
            (ρ ^ ((2 * (d + 1)) * (2 * (d + 1) - 1) / 2) + δ) <
          1 / ((2 * Q) ^ (d * (2 * (d + 1))) *
            (2 * H) ^ (2 * (d + 1))) →
        (targetLinearMatrix d
          (fun i => (p i : ℝ) / q i)
          (fun i => (r i : ℝ) / s i)).det = 0 := by
  obtain ⟨K, hK0, hK⟩ :=
    exists_targetLinearMatrix_analytic_upper_bound hf d hαβ hI
  refine ⟨K, hK0, ?_⟩
  intro Q H ρ δ p r q s hQ hH hq hs hqQ hsH
    hρ0 hρ1 hδ0 hδ1 hxI hxρ herr hsmall
  apply targetLinearMatrix_det_eq_zero_of_lt d p r q s hq hs
    hQ hH hqQ hsH
  exact (hK ρ δ hρ0 hρ1 hδ0 hδ1
    (fun i => (p i : ℝ) / q i)
    (fun i => (r i : ℝ) / s i)
    hxI hxρ herr).trans_lt hsmall

end MahlerLean
