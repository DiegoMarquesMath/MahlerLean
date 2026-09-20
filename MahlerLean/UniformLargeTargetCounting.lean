import MahlerLean.UniformSublevelThreshold

open Set
noncomputable section
namespace MahlerLean

/-- All counting constants and the source-height threshold are chosen before
the large-target exponent u and the source cell. The sublevel smallness
condition is now a consequence, not a hypothesis. -/
theorem exists_uniform_largeTarget_cell_counting_bound
    {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hf : AnalyticOnNhd ℝ f U) (A : ℕ)
    {a b K₀ X : ℝ} (hab : a < b) (hI : Icc a b ⊆ U)
    (hK₀ : 0 ≤ K₀) (hX : 1 ≤ X)
    (hW : ∀ d : ℕ, 2 ≤ d → d ≤ wronskianDegreeCutoff A →
      ∀ z ∈ Icc a b, rationalWronskian f d z ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∃ R : ℕ, 0 < R ∧
    ∃ Q₀ : ℝ, 1 ≤ Q₀ ∧ ∀ Q : ℕ, Q₀ ≤ (Q : ℝ) →
      ∀ u : ℝ, (1 : ℝ) / 5 ≤ u → 97 * u < (A : ℝ) →
      ∀ c : ℝ, a ≤ c → c < b → ∀ S : Finset ℚ,
        (∀ r ∈ S, |(r : ℝ)| ≤ X) →
        (∀ r ∈ S, r.den < 2 * Q) →
        (∀ r ∈ S, (r : ℝ) ∈ Icc c b) →
        (∀ r ∈ S, (r : ℝ) - c ≤ (Q : ℝ) ^ (-largeTargetKappa u)) →
        (∀ r ∈ S, ∃ y : ℚ, (y.den : ℝ) ≤ 2 * (Q : ℝ) ^ u ∧
          |(y : ℝ) - f r| ≤ K₀ * (Q : ℝ) ^ (-largeTargetS A u)) →
        (S.card : ℝ) ≤ 4 * (Q : ℝ) ^ 2 *
          (C * ((largeTargetN u : ℝ) *
            (X ^ largeTargetDegree u * (K₀ * (Q : ℝ) ^ (-largeTargetS A u)))) ^
            (((largeTargetN u - 1 : ℕ) : ℝ)⁻¹)) + R := by
  let D := wronskianDegreeCutoff A
  have hD : 2 ≤ D := le_max_left _ _
  obtain ⟨C, hC, R, hR, eps, heps, _, hcount⟩ :=
    exists_uniform_degree_counting_data hU hf D hD hab.le hI hW
  obtain ⟨Qdet, hQdet, hwitness⟩ :=
    exists_largeTarget_witnesses_all_det_zero hf A hab hI hK₀
  let L : ℝ := (2 * (D + 1) : ℕ) * (X ^ D * K₀)
  refine ⟨C, hC, R, hR, max Qdet (L / eps + 1),
    hQdet.trans (le_max_left _ _), ?_⟩
  intro Q hQ u hu huA c hac hcb S hxX hden hx hxρ hw
  have hQd : Qdet ≤ (Q : ℝ) := (le_max_left _ _).trans hQ
  have hQ1 : (1 : ℝ) ≤ Q := hQdet.trans hQd
  have hQpos : 0 < Q := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hQ1)
  have hd := largeTargetDegree_le_wronskianCutoff A u (by linarith : u < (A : ℝ) / 97)
  have hs : 1 ≤ largeTargetS A u := by
    have := largeTargetS_ge_97u A u hu huA
    linarith
  have hsmall := scaled_error_lt_of_uniform_threshold hQ1 hX hK₀ heps hd hs
    ((le_max_right _ _).trans hQ)
  obtain ⟨y, hy, hdet⟩ := hwitness Q hQd u hu huA c hac hcb S
    (fun r hr ↦ by exact_mod_cast (hden r hr).le) hx hxρ hw
  exact hcount (largeTargetDegree u) (largeTargetDegree_ge_two u hu) hd
    S (fun r ↦ (y r : ℝ)) hQpos hdet hX hxX
    (fun r hr ↦ ⟨hac.trans (hx r hr).1, (hx r hr).2⟩)
    (mul_nonneg hK₀ (Real.rpow_nonneg (Nat.cast_nonneg Q) _))
    (fun r hr ↦ (hy r hr).2) hden hsmall

/-- A single constant bounds every admissible large-target cell. -/
theorem exists_uniform_largeTarget_cell_card_bound
    {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hf : AnalyticOnNhd ℝ f U) (A : ℕ)
    {a b K₀ X : ℝ} (hab : a < b) (hI : Icc a b ⊆ U)
    (hK₀ : 0 ≤ K₀) (hX : 1 ≤ X)
    (hW : ∀ d : ℕ, 2 ≤ d → d ≤ wronskianDegreeCutoff A →
      ∀ z ∈ Icc a b, rationalWronskian f d z ≠ 0) :
    ∃ M : ℝ, 0 < M ∧
    ∃ Q₀ : ℝ, 1 ≤ Q₀ ∧ ∀ Q : ℕ, Q₀ ≤ (Q : ℝ) →
      ∀ u : ℝ, (1 : ℝ) / 5 ≤ u → 97 * u < (A : ℝ) →
      ∀ c : ℝ, a ≤ c → c < b → ∀ S : Finset ℚ,
        (∀ r ∈ S, |(r : ℝ)| ≤ X) →
        (∀ r ∈ S, r.den < 2 * Q) →
        (∀ r ∈ S, (r : ℝ) ∈ Icc c b) →
        (∀ r ∈ S, (r : ℝ) - c ≤ (Q : ℝ) ^ (-largeTargetKappa u)) →
        (∀ r ∈ S, ∃ y : ℚ, (y.den : ℝ) ≤ 2 * (Q : ℝ) ^ u ∧
          |(y : ℝ) - f r| ≤ K₀ * (Q : ℝ) ^ (-largeTargetS A u)) →
        (S.card : ℝ) ≤ M := by
  obtain ⟨C, hC, R, hR, Q₀, hQ₀, hcount⟩ :=
    exists_uniform_largeTarget_cell_counting_bound hU hf A hab hI hK₀ hX hW
  let D := wronskianDegreeCutoff A
  let L : ℝ := (2 * (D + 1) : ℕ) * (X ^ D * K₀)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  refine ⟨4 * C * max 1 L + R, by positivity, Q₀, hQ₀, ?_⟩
  intro Q hQ u hu huA c hac hcb S hxX hden hx hxρ hw
  have hb := hcount Q hQ u hu huA c hac hcb S hxX hden hx hxρ hw
  have hd := largeTargetDegree_le_wronskianCutoff A u (by linarith : u < (A : ℝ) / 97)
  have hcast : ((largeTargetN u - 1 : ℕ) : ℝ) = largeTargetDen u := by
    unfold largeTargetN largeTargetDen
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * (largeTargetDegree u + 1))]
    push_cast
    ring
  have hden1 : 1 ≤ largeTargetDen u := by
    unfold largeTargetDen
    have := Nat.cast_nonneg (α := ℝ) (largeTargetDegree u)
    linarith
  have ht0 : 0 ≤ (((largeTargetN u - 1 : ℕ) : ℝ)⁻¹) := by positivity
  have ht1 : (((largeTargetN u - 1 : ℕ) : ℝ)⁻¹) ≤ 1 := by
    rw [hcast]
    exact (inv_le_one₀ (largeTargetDen_pos u)).mpr hden1
  have hst : 2 ≤ largeTargetS A u * (((largeTargetN u - 1 : ℕ) : ℝ)⁻¹) := by
    simpa only [hcast, div_eq_mul_inv] using (largeTargetFareyExponent_gt_two A u hu huA).le
  have hE := scaled_error_le_uniform_coefficient hX hK₀
    (Real.rpow_nonneg (Nat.cast_nonneg Q) (-largeTargetS A u)) hd
  have hb' := farey_sublevel_bound_le_constant (hQ₀.trans hQ) hC.le hL
    (show 0 ≤ (largeTargetN u : ℝ) *
      (X ^ largeTargetDegree u * (K₀ * (Q : ℝ) ^ (-largeTargetS A u))) by positivity)
    hE ht0 ht1 hst
  exact hb.trans (add_le_add_right hb' _)

/-- Interval-only version: the source-coordinate bound is fixed by the parent interval. -/
theorem exists_uniform_largeTarget_interval_cell_card_bound
    {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hf : AnalyticOnNhd ℝ f U) (A : ℕ)
    {a b K₀ : ℝ} (hab : a < b) (hI : Icc a b ⊆ U)
    (hK₀ : 0 ≤ K₀)
    (hW : ∀ d : ℕ, 2 ≤ d → d ≤ wronskianDegreeCutoff A →
      ∀ z ∈ Icc a b, rationalWronskian f d z ≠ 0) :
    ∃ M : ℝ, 0 < M ∧
    ∃ Q₀ : ℝ, 1 ≤ Q₀ ∧ ∀ Q : ℕ, Q₀ ≤ (Q : ℝ) →
      ∀ u : ℝ, (1 : ℝ) / 5 ≤ u → 97 * u < (A : ℝ) →
      ∀ c : ℝ, a ≤ c → c < b → ∀ S : Finset ℚ,
        (∀ r ∈ S, r.den < 2 * Q) →
        (∀ r ∈ S, (r : ℝ) ∈ Icc c b) →
        (∀ r ∈ S, (r : ℝ) - c ≤ (Q : ℝ) ^ (-largeTargetKappa u)) →
        (∀ r ∈ S, ∃ y : ℚ, (y.den : ℝ) ≤ 2 * (Q : ℝ) ^ u ∧
          |(y : ℝ) - f r| ≤ K₀ * (Q : ℝ) ^ (-largeTargetS A u)) →
        (S.card : ℝ) ≤ M := by
  let X : ℝ := max 1 (max |a| |b|)
  have hX : 1 ≤ X := le_max_left _ _
  obtain ⟨M, hM, Q₀, hQ₀, hcount⟩ :=
    exists_uniform_largeTarget_cell_card_bound hU hf A hab hI hK₀ hX hW
  refine ⟨M, hM, Q₀, hQ₀, ?_⟩
  intro Q hQ u hu huA c hac hcb S hden hx hxρ hw
  apply hcount Q hQ u hu huA c hac hcb S _ hden hx hxρ hw
  intro r hr
  have hAX : |a| ≤ X := (le_max_left _ _).trans (le_max_right _ _)
  have hBX : |b| ≤ X := (le_max_right _ _).trans (le_max_right _ _)
  apply abs_le.mpr
  constructor
  · have := neg_abs_le a
    have := (hx r hr).1
    linarith
  · have := le_abs_self b
    have := (hx r hr).2
    linarith

end MahlerLean
