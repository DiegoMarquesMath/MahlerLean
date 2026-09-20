import MahlerLean.DeterminantScaleComparison

open Set
noncomputable section
namespace MahlerLean

/-- With the manuscript's adaptive scales, a single threshold works for
all large target blocks and every cell of the fixed parent interval.
There is no remaining determinant-size or perturbation-smallness hypothesis. -/
theorem exists_largeTarget_det_zero_uniform_threshold
    {f : ℝ → ℝ} {U : Set ℝ} (hf : AnalyticOnNhd ℝ f U)
    (A : ℕ) {a b K₀ : ℝ} (hab : a < b) (hI : Icc a b ⊆ U)
    (hK₀ : 0 ≤ K₀) :
    ∃ Q₀ : ℝ, 1 ≤ Q₀ ∧ ∀ Q : ℝ, Q₀ ≤ Q →
      ∀ u : ℝ, (1 : ℝ) / 5 ≤ u → 97 * u < (A : ℝ) →
      ∀ c : ℝ, a ≤ c → c < b →
      ∀ (p r : Fin (largeTargetN u) → ℤ)
        (q s : Fin (largeTargetN u) → ℕ),
        (∀ i, 0 < q i) → (∀ i, 0 < s i) →
        (∀ i, (q i : ℝ) ≤ 2 * Q) →
        (∀ i, (s i : ℝ) ≤ 2 * Q ^ u) →
        (∀ i, (p i : ℝ) / q i ∈ Icc c b) →
        (∀ i, (p i : ℝ) / q i - c ≤ Q ^ (-largeTargetKappa u)) →
        (∀ i, |(r i : ℝ) / s i - f ((p i : ℝ) / q i)| ≤
          K₀ * Q ^ (-largeTargetS A u)) →
        (targetLinearMatrix (largeTargetDegree u)
          (fun i ↦ (p i : ℝ) / q i) (fun i ↦ (r i : ℝ) / s i)).det = 0 := by
  let D := wronskianDegreeCutoff A
  obtain ⟨K, hK, hzero⟩ := exists_targetLinearMatrix_det_zero_uniform_cells hf D hab hI
  let B : ℝ := K * 2 ^ (D * (2 * (D + 1)) + 2 * (D + 1))
  refine ⟨max 1 (max (K₀ ^ 5) (B + 1)), le_max_left _ _, ?_⟩
  intro Q hQ₀ u hu huA c hac hcb p r q s hq hs hqQ hsQ hx hxρ herr
  have hQ : 1 ≤ Q := (le_max_left _ _).trans hQ₀
  have hpos : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have hKQ : K₀ ^ 5 ≤ Q := (le_max_left _ _).trans ((le_max_right _ _).trans hQ₀)
  have hBQ : B < Q := by
    have : B + 1 ≤ Q := (le_max_right _ _).trans ((le_max_right _ _).trans hQ₀)
    linarith
  have hd := largeTargetDegree_le_wronskianCutoff A u (by linarith : u < (A : ℝ) / 97)
  have hκ : 0 ≤ largeTargetKappa u := by
    unfold largeTargetKappa
    apply div_nonneg _ (largeTargetDen_pos u).le
    have : (0 : ℝ) ≤ largeTargetDegree u := Nat.cast_nonneg _
    positivity
  have hρ1 : Q ^ (-largeTargetKappa u) ≤ 1 := by
    calc
      Q ^ (-largeTargetKappa u) ≤ Q ^ (0 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hQ (neg_nonpos.mpr hκ)
      _ = 1 := Real.rpow_zero Q
  have hcompare := determinant_scale_comparison hQ hK hd hBQ
    (κ := largeTargetKappa u) (u := u) (by
      have hg := largeTarget_determinant_exponent_gap u hu
      simpa only [largeTargetN, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add,
        Nat.cast_one, mul_div_assoc, mul_assoc] using hg)
  exact hzero (largeTargetDegree u) hd c hac hcb p r q s hpos
    (Real.rpow_pos_of_pos hpos u) hq hs hqQ hsQ
    (Real.rpow_pos_of_pos hpos _) hρ1
    (mul_nonneg hK₀ (Real.rpow_nonneg hpos.le _))
    (largeTarget_vertical_error_le_radius_power A u hu huA hQ hK₀ hKQ)
    hx hxρ herr hcompare

end MahlerLean
