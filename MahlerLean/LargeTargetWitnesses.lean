import MahlerLean.LargeTargetDeterminantVanishing
import MahlerLean.TargetLinearCounting

open Set
noncomputable section
namespace MahlerLean

/-- Choose one rational witness per source point, then apply the uniform
large-block determinant theorem to every tuple of source points. Repetitions
are allowed, as required by the linear-dependence counting bridge. -/
theorem exists_largeTarget_witnesses_all_det_zero
    {f : ℝ → ℝ} {U : Set ℝ} (hf : AnalyticOnNhd ℝ f U)
    (A : ℕ) {a b K₀ : ℝ} (hab : a < b) (hI : Icc a b ⊆ U)
    (hK₀ : 0 ≤ K₀) :
    ∃ Q₀ : ℝ, 1 ≤ Q₀ ∧ ∀ Q : ℝ, Q₀ ≤ Q →
      ∀ u : ℝ, (1 : ℝ) / 5 ≤ u → 97 * u < (A : ℝ) →
      ∀ c : ℝ, a ≤ c → c < b → ∀ S : Finset ℚ,
        (∀ r ∈ S, (r.den : ℝ) ≤ 2 * Q) →
        (∀ r ∈ S, (r : ℝ) ∈ Icc c b) →
        (∀ r ∈ S, (r : ℝ) - c ≤ Q ^ (-largeTargetKappa u)) →
        (∀ r ∈ S, ∃ y : ℚ, (y.den : ℝ) ≤ 2 * Q ^ u ∧
          |(y : ℝ) - f r| ≤ K₀ * Q ^ (-largeTargetS A u)) →
        ∃ y : ℚ → ℚ,
          (∀ r ∈ S, ((y r).den : ℝ) ≤ 2 * Q ^ u ∧
            |(y r : ℝ) - f r| ≤ K₀ * Q ^ (-largeTargetS A u)) ∧
          ∀ rows : Fin (largeTargetN u) → ↑S,
            (targetLinearMatrix (largeTargetDegree u)
              (fun i ↦ (rows i : ℝ)) (fun i ↦ (y (rows i) : ℝ))).det = 0 := by
  classical
  obtain ⟨Q₀, hQ₀, hzero⟩ := exists_largeTarget_det_zero_uniform_threshold hf A hab hI hK₀
  refine ⟨Q₀, hQ₀, ?_⟩
  intro Q hQ u hu huA c hac hcb S hden hx hxρ hw
  let y : ℚ → ℚ := fun r ↦ if hr : r ∈ S then (hw r hr).choose else 0
  have hy (r : ℚ) (hr : r ∈ S) :
      ((y r).den : ℝ) ≤ 2 * Q ^ u ∧
        |(y r : ℝ) - f r| ≤ K₀ * Q ^ (-largeTargetS A u) := by
    simpa only [y, dif_pos hr] using (hw r hr).choose_spec
  refine ⟨y, hy, ?_⟩
  intro rows
  have hz := hzero Q hQ u hu huA c hac hcb
    (fun i ↦ (rows i).val.num) (fun i ↦ (y (rows i)).num)
    (fun i ↦ (rows i).val.den) (fun i ↦ (y (rows i)).den)
    (fun i ↦ (rows i).val.den_pos) (fun i ↦ (y (rows i)).den_pos)
    (fun i ↦ hden _ (rows i).property)
    (fun i ↦ (hy _ (rows i).property).1)
    (fun i ↦ by simpa only [← Rat.cast_def] using hx _ (rows i).property)
    (fun i ↦ by simpa only [← Rat.cast_def] using hxρ _ (rows i).property)
    (fun i ↦ by simpa only [← Rat.cast_def] using (hy _ (rows i).property).2)
  simpa only [← Rat.cast_def] using hz

/-- Counting in a large-target cell with existential rational witnesses.
All maximal determinant hypotheses have been discharged. The remaining
smallness condition is the sublevel threshold, to be absorbed uniformly
when the finite adaptive degree range is assembled. -/
theorem exists_largeTarget_cell_counting_data
    {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hf : AnalyticOnNhd ℝ f U) (A : ℕ)
    {a b K₀ : ℝ} (hab : a < b) (hI : Icc a b ⊆ U) (hK₀ : 0 ≤ K₀)
    (hW : ∀ d : ℕ, 2 ≤ d → d ≤ wronskianDegreeCutoff A →
      ∀ z ∈ Icc a b, rationalWronskian f d z ≠ 0) :
    ∃ Q₀ : ℝ, 1 ≤ Q₀ ∧ ∀ u : ℝ,
      (1 : ℝ) / 5 ≤ u → 97 * u < (A : ℝ) →
      ∃ C : ℝ, 0 < C ∧ ∃ R : ℕ, 0 < R ∧
      ∃ eps0 : ℝ, 0 < eps0 ∧ eps0 < 1 ∧
      ∀ (Q : ℕ), Q₀ ≤ (Q : ℝ) → ∀ c : ℝ, a ≤ c → c < b →
      ∀ (S : Finset ℚ) (X : ℝ), 1 ≤ X →
        (∀ r ∈ S, |(r : ℝ)| ≤ X) →
        (∀ r ∈ S, r.den < 2 * Q) →
        (∀ r ∈ S, (r : ℝ) ∈ Icc c b) →
        (∀ r ∈ S, (r : ℝ) - c ≤ (Q : ℝ) ^ (-largeTargetKappa u)) →
        (∀ r ∈ S, ∃ y : ℚ, (y.den : ℝ) ≤ 2 * (Q : ℝ) ^ u ∧
          |(y : ℝ) - f r| ≤ K₀ * (Q : ℝ) ^ (-largeTargetS A u)) →
        (largeTargetN u : ℝ) *
          (X ^ largeTargetDegree u * (K₀ * (Q : ℝ) ^ (-largeTargetS A u))) < eps0 →
        (S.card : ℝ) ≤ 4 * (Q : ℝ) ^ 2 *
          (C * ((largeTargetN u : ℝ) *
            (X ^ largeTargetDegree u * (K₀ * (Q : ℝ) ^ (-largeTargetS A u)))) ^
            (((largeTargetN u - 1 : ℕ) : ℝ)⁻¹)) + R := by
  obtain ⟨Q₀, hQ₀, hwitness⟩ := exists_largeTarget_witnesses_all_det_zero hf A hab hI hK₀
  refine ⟨Q₀, hQ₀, ?_⟩
  intro u hu huA
  have hd := largeTargetDegree_le_wronskianCutoff A u (by linarith : u < (A : ℝ) / 97)
  obtain ⟨C, hC, R, hR, eps0, heps, heps1, hcount⟩ :=
    exists_targetLinear_counting_bound_of_all_det_zero hU hf
      (largeTargetDegree u) hab.le hI (hW _ (largeTargetDegree_ge_two u hu) hd)
  refine ⟨C, hC, R, hR, eps0, heps, heps1, ?_⟩
  intro Q hQ c hac hcb S X hX hxX hden hx hxρ hw hsmall
  have hQpos : 0 < Q := by
    have : (1 : ℝ) ≤ Q := hQ₀.trans hQ
    exact_mod_cast (lt_of_lt_of_le zero_lt_one this)
  obtain ⟨y, hy, hdet⟩ := hwitness Q hQ u hu huA c hac hcb S
    (fun r hr ↦ by exact_mod_cast (hden r hr).le) hx hxρ hw
  exact hcount S (fun r ↦ (y r : ℝ)) hQpos hdet hX hxX
    (fun r hr ↦ ⟨hac.trans (hx r hr).1, (hx r hr).2⟩)
    (mul_nonneg hK₀ (Real.rpow_nonneg (Nat.cast_nonneg Q) _))
    (fun r hr ↦ (hy r hr).2) hden hsmall

end MahlerLean
