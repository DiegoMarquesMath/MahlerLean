import MahlerLean.DangerousSourceDecomposition

open Set
noncomputable section
namespace MahlerLean

/-- Proposition 5.1 with an explicit fixed image bound F. The leading
constant is chosen before J and A, and both later constants before H. -/
theorem proposition_5_1_of_fixed_bounds
    {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (hf : AnalyticOnNhd ℝ f U)
    {a b F m M : ℝ} (hIU : Icc a b ⊆ U)
    (hF : 0 ≤ F) (hM : 0 ≤ M) (hm : 0 < m)
    (hfF : ∀ x ∈ Icc a b, |f x| ≤ F)
    (hdm : ∀ x ∈ Icc a b, m ≤ |deriv f x|) :
    ∃ C_low : ℝ, 0 < C_low ∧
      ∀ l u : ℝ, l < u → Icc l u ⊆ Icc a b →
      ∀ A : ℕ, 3 ≤ A →
        (∀ d : ℕ, 2 ≤ d → d ≤ wronskianDegreeCutoff A →
          ∀ z ∈ Icc l u, rationalWronskian f d z ≠ 0) →
        ∃ C : ℝ, 0 < C ∧ ∃ Q₀ : ℕ, 0 < Q₀ ∧
          ∀ H Q : ℕ, 2 ≤ H → Q₀ ≤ Q →
            ((dangerousSources f l u M Q A H).card : ℝ) ≤
              C_low*(Q : ℝ)^2*((H : ℝ)^98)⁻¹+C*(Q : ℝ)^((17 : ℝ)/10) := by
  classical
  have hd : ∀ x ∈ Icc a b, DifferentiableAt ℝ f x :=
    fun x hx ↦ (hf x (hIU hx)).differentiableAt
  obtain ⟨Clow, Cerr, hClow, hCerr, hsmall⟩ :=
    exists_smallTarget_counting_of_derivative_bounds hF hM hm hfF hd hdm
  refine ⟨Clow, hClow, ?_⟩
  intro l u hlu hJ A hA hW
  obtain ⟨Clarge, hClarge, Qlarge, hQlarge, hlarge⟩ :=
    exists_largeTarget_original_margin_card_bound hU hf A hlu (hJ.trans hIU) hM hW
  refine ⟨Cerr+Clarge, add_pos hCerr hClarge, ⌈Qlarge⌉₊,
    Nat.ceil_pos.mpr (by linarith), ?_⟩
  intro H Q hH hQ
  have hQQ : Qlarge ≤ (Q : ℝ) := (Nat.le_ceil Qlarge).trans (by exact_mod_cast hQ)
  have hQ1 : (1 : ℝ) ≤ Q := by linarith
  have hQpos : 0 < Q := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hQ1)
  have hHpos : 0 < H := by omega
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast (show 1 ≤ H by omega)
  let S := dangerousSources f l u M Q A H
  let small := S.filter (HasSmallTargetWitness f M Q A H)
  let large := S.filter (fun r ↦ ¬HasSmallTargetWitness f M Q A H r)
  have hsrc (r : ℚ) (hr : r ∈ S) : r ∈ sourceFractions l u Q :=
    (Finset.mem_filter.mp hr).1
  have hx (r : ℚ) (hr : r ∈ S) : (r : ℝ) ∈ Icc l u := by
    have hh := (mem_sourceFractions l u Q r).mp (hsrc r hr)
    exact ⟨hh.1, hh.2.1⟩
  have hden (r : ℚ) (hr : r ∈ S) : r.den < 2*Q :=
    ((mem_sourceFractions l u Q r).mp (hsrc r hr)).2.2.2
  have hs := hsmall A Q hA hQpos H hH1 small
    (fun r hr ↦ hden r (Finset.mem_filter.mp hr).1)
    (fun r hr ↦ hJ (hx r (Finset.mem_filter.mp hr).1))
    (fun r hr ↦ (Finset.mem_filter.mp hr).2)
  have hl := hlarge Q hQQ H hH1 large
    (fun r hr ↦ hden r (Finset.mem_filter.mp hr).1)
    (fun r hr ↦ hx r (Finset.mem_filter.mp hr).1)
    (fun r hr ↦ (hasTargetWitness_small_or_large hHpos
      (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).2).resolve_left
        (Finset.mem_filter.mp hr).2)
  have hc : (small.card : ℝ)+(large.card : ℝ) = (S.card : ℝ) := by
    exact_mod_cast (Finset.filter_card_add_filter_neg_card_eq_card
      (s := S) (HasSmallTargetWitness f M Q A H))
  have hp : (Q : ℝ)^((2 : ℝ)/5) ≤ (Q : ℝ)^((17 : ℝ)/10) :=
    Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num)
  change (S.card : ℝ) ≤ _
  nlinarith [mul_le_mul_of_nonneg_left hp hCerr.le]

/-- Two-height counting on analytic graphs (Proposition 5.1).
The image bound is supplied by compactness. The leading constant is uniform
in the subinterval and A; the remainder and natural threshold are uniform in H. -/
theorem proposition_5_1
    {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (hf : AnalyticOnNhd ℝ f U)
    {a b m M : ℝ} (hIU : Icc a b ⊆ U)
    (hM : 0 ≤ M) (hm : 0 < m)
    (hdm : ∀ x ∈ Icc a b, m ≤ |deriv f x|) :
    ∃ C_low : ℝ, 0 < C_low ∧
      ∀ l u : ℝ, l < u → Icc l u ⊆ Icc a b →
      ∀ A : ℕ, 3 ≤ A →
        (∀ d : ℕ, 2 ≤ d → d ≤ wronskianDegreeCutoff A →
          ∀ z ∈ Icc l u, rationalWronskian f d z ≠ 0) →
        ∃ C : ℝ, 0 < C ∧ ∃ Q₀ : ℕ, 0 < Q₀ ∧
          ∀ H Q : ℕ, 2 ≤ H → Q₀ ≤ Q →
            ((dangerousSources f l u M Q A H).card : ℝ) ≤
              C_low*(Q : ℝ)^2*((H : ℝ)^98)⁻¹+C*(Q : ℝ)^((17 : ℝ)/10) := by
  have hcont : ContinuousOn f (Icc a b) :=
    fun x hx ↦ (hf x (hIU hx)).continuousAt.continuousWithinAt
  obtain ⟨F, hF⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  exact proposition_5_1_of_fixed_bounds hU hf hIU (le_max_left 0 F) hM hm
    (fun x hx ↦ (show |f x| ≤ F by simpa only [Real.norm_eq_abs] using hF x hx).trans (le_max_right 0 F)) hdm

/-- Proposition 5.1 supplies the uniform danger bound used by fusion. -/
theorem proposition_5_1_uniformDangerBound
    {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (hf : AnalyticOnNhd ℝ f U)
    {a b m M : ℝ} (hIU : Icc a b ⊆ U)
    (hM : 0 ≤ M) (hm : 0 < m)
    (hdm : ∀ x ∈ Icc a b, m ≤ |deriv f x|) :
    ∃ C_low : ℝ, 0 < C_low ∧
      ∀ l u : ℝ, l < u → Icc l u ⊆ Icc a b →
      ∀ A : ℕ, 3 ≤ A →
        (∀ d : ℕ, 2 ≤ d → d ≤ wronskianDegreeCutoff A →
          ∀ z ∈ Icc l u, rationalWronskian f d z ≠ 0) →
        ∃ C : ℝ, 0 < C ∧ HasUniformDangerBound f l u M C_low C A := by
  obtain ⟨C_low, hpos, hbound⟩ := proposition_5_1 hU hf hIU hM hm hdm
  refine ⟨C_low, hpos, ?_⟩
  intro l u hlu hJ A hA hW
  obtain ⟨C, hC, Q₀, _, hQ₀⟩ := hbound l u hlu hJ A hA hW
  exact ⟨C, hC, Q₀, fun H hH Q hQ ↦ hQ₀ H Q hH hQ⟩

end MahlerLean
