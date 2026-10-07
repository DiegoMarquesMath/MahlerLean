import MahlerLean.CantorTopology
import MahlerLean.RationalWronskianNonvanishing

/-!
The current manuscript's Theorem 1.1.

This file assembles the analytic inputs already used by the single-point
escape theorem with the binary Cantor refinement.  The legacy declarations
theorem_1_1 and theorem_1_2 are intentionally left unchanged; the theorem
below follows the current manuscript numbering semantically.
-/

noncomputable section
namespace MahlerLean

open Set

/-- Current Theorem 1.1: every nonempty open subinterval contains a compact
perfect totally disconnected set of Liouville numbers whose images have
irrationality exponent at most 100, with one common target cutoff. -/
theorem current_theorem_1_1
    {f : ℝ → ℝ} {U V : Set ℝ}
    (hU : IsOpen U) (hconn : IsPreconnected U)
    (hf : AnalyticOnNhd ℝ f U) (hnr : ¬ IsRationalOn f U)
    (hV : IsOpen V) (hne : V.Nonempty) (hVU : V ⊆ U) :
    ∃ K : Set ℝ, ∃ B : ℕ,
      K.Nonempty ∧
      IsCompact K ∧
      Perfect K ∧
      IsTotallyDisconnected K ∧
      K ⊆ V ∧
      2 ≤ B ∧
      (∀ x ∈ K, Liouville x) ∧
      (∀ x ∈ K, EventualTargetAvoidance (f x) 100 B) ∧
      (∀ x ∈ K, irrationalityExponent (f x) ≤ (100 : EReal)) := by
  have hnc : ∃ x ∈ U, ∃ y ∈ U, f x ≠ f y :=
    nonconstant_of_not_rational (hne.mono hVU) hnr
  obtain ⟨c, d0, hcd, hcdV⟩ := hV.exists_Ioo_subset hne
  obtain ⟨a, hca, had⟩ := exists_between hcd
  obtain ⟨b, hab, hbd⟩ := exists_between had
  have hI_V : Icc a b ⊆ V := by
    intro x hx
    exact hcdV ⟨hca.trans_le hx.1, hx.2.trans_lt hbd⟩
  have hI_U : Icc a b ⊆ U := hI_V.trans hVU
  obtain ⟨l, u, m, M, hal, hlu, hub, hm, hM, hdm, hdM⟩ :=
    exists_analytic_derivative_interval hU hconn hf hnc a b hab hI_U
  have hluV : Icc l u ⊆ V := by
    intro x hx
    exact hI_V ⟨hal.le.trans hx.1, hx.2.trans hub.le⟩
  have hluU : Icc l u ⊆ U := hluV.trans hVU
  obtain ⟨Clow, hClow, hcount⟩ :=
    proposition_5_1_uniformDangerBound hU hf hluU hM hm hdm
  have hW : ∀ deg : ℕ, 2 ≤ deg →
      ∃ y ∈ U, rationalWronskian f deg y ≠ 0 := by
    intro deg _hdeg
    exact exists_rationalWronskian_ne_zero_of_not_rational
      hU (hne.mono hVU) hconn hf hnr deg
  let e : WronskianCountingInputs f := {
    domain := U
    domain_preconnected := hconn
    analytic := hf
    left := l
    right := u
    nondegenerate := hlu
    interval_subset := hluU
    M := M
    Clow := Clow
    M_nonneg := hM
    Clow_nonneg := hClow.le
    deriv_bound := hdM
    wronskian_nonzero := hW
    counting := by
      intro n l' u' hl'u' hsub hWr
      obtain ⟨C, _hCpos, hC⟩ :=
        hcount l' u' hl'u' hsub (n + 3) (by omega)
          (fun deg hdeg hD =>
            hWr deg (Finset.mem_Icc.mpr ⟨hdeg, hD⟩))
      exact ⟨C, hC⟩ }
  let D : FusionInputs f := e.toUniformCountingInputs.toFusionInputs
  let K : Set ℝ := cantorLimitSet D
  let B : ℕ := (initialFusionStage D).cutoff
  have hKV : K ⊆ V := by
    intro x hx
    have hxu : x ∈ Ioo l u := by
      simpa [K, D, e] using cantorLimitSet_subset_ambient D hx
    exact hluV ⟨hxu.1.le, hxu.2.le⟩
  refine ⟨K, B,
    ?_, ?_, ?_, ?_, hKV, ?_, ?_, ?_, ?_⟩
  · simpa [K] using cantorLimitSet_nonempty D
  · simpa [K] using cantorLimitSet_compact D
  · simpa [K] using cantorLimitSet_perfect D
  · simpa [K] using cantorLimitSet_isTotallyDisconnected D
  · simpa [B] using (initialFusionStage D).cutoff_ge_two
  · intro x hx
    exact cantorLimitSet_liouville D (by simpa [K] using hx)
  · intro x hx
    simpa [B] using
      cantorLimitSet_target_avoidance D (by simpa [K] using hx)
  · intro x hx
    exact cantorLimitSet_irrationalityExponent_le D (by simpa [K] using hx)

/-- Current Corollary 1.2, under a numbering-stable descriptive alias. -/
theorem current_corollary_1_2
    {f : ℝ → ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hconn : IsPreconnected U)
    (hf : AnalyticOnNhd ℝ f U)
    (hpres : ∀ x ∈ U, Liouville x → Liouville (f x)) :
    IsRationalOn f U :=
  rationalOn_of_preserves_liouville hU hconn hf hpres

end MahlerLean
