import MahlerLean.FiniteAvoidance
import MahlerLean.FusionScale
import MahlerLean.FusionConclusion

/-!
One complete successor step of fusion, conditional on the two counting
inputs and a finite set Z to avoid at the next stage. The step chooses Q
after all quantities controlling its thresholds, then a safe rational
center, then a positive-length interval with the required invariants.

Constructing the full infinite sequence and supplying the analytic
counting/Wronskian hypotheses remain separate tasks.
-/

namespace MahlerLean

open Set

/-- The output of one fusion step. Its existence is proved below from
explicit local hypotheses; no instance or axiom provides this data. -/
structure SuccessorInterval (f : ℝ → ℝ) (Z : Finset ℝ)
    (l u Clow cF : ℝ) (Q A H : ℕ) (r : ℚ) where
  left : ℝ
  right : ℝ
  nondegenerate : left < right
  nested : Icc left right ⊆ Ioo l u
  length : right - left = fusionRadius Q A / ((Z.card : ℝ) + 2)
  avoids : ∀ x ∈ Icc left right, x ∉ Z
  source : ∀ x ∈ Icc left right,
    0 < |x - (r : ℝ)| ∧ |x - (r : ℝ)| < (((r.den : ℕ) : ℝ) ^ A)⁻¹
  cutoff_increases : H < nextCutoff Q A
  target : ∀ x ∈ Icc left right, ∀ a : ℤ, ∀ b : ℕ,
    H ≤ b → b < nextCutoff Q A →
    ((b : ℝ) ^ 100)⁻¹ < |f x - (a : ℝ) / (b : ℝ)|
  tail : Clow * (((nextCutoff Q A : ℕ) : ℝ) ^ 98)⁻¹ ≤
    (cF / 4) * ((right - left) / 3)

/-- The successor interval once Q and its safe center have been chosen.
The scale and geometric assumptions are exactly the local conditions
needed from (Q2)--(Q4) and Lemma 6.1. -/
theorem successor_from_safe_center
    (f : ℝ → ℝ) (Z : Finset ℝ) (l u M Clow cF : ℝ)
    (Q A H : ℕ) (r : ℚ)
    (hinterval : l < u) (hQ : 2 ≤ Q) (hH : 2 ≤ H)
    (hM : 0 ≤ M) (hC : 0 ≤ Clow)
    (hf : ∀ y ∈ Icc l u, DifferentiableAt ℝ f y)
    (hderiv : ∀ y ∈ Icc l u, |deriv f y| ≤ M)
    (hrleft : l + (u - l) / 3 ≤ (r : ℝ))
    (hrright : (r : ℝ) ≤ u - (u - l) / 3)
    (hden : r.den < 2 * Q) (hsafe : IsSafeCenter f M Q A H r)
    (hfit : fusionRadius Q A < (u - l) / 3)
    (hheight : 2 * (H : ℝ) + 2 ≤ targetCutoff Q A)
    (hscale : 3 * Clow * ((Z.card : ℝ) + 2) * (2 : ℝ) ^ (A + 98) *
      (targetCutoff Q A)⁻¹ ≤ cF / 4) :
    Nonempty (SuccessorInterval f Z l u Clow cF Q A H r) := by
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hRpos : 0 < fusionRadius Q A := by unfold fusionRadius; positivity
  obtain ⟨a, b, hab, hsub, hlen, havoid⟩ :=
    exists_next_interval_in_parent Z l u (r : ℝ) (fusionRadius Q A)
      hRpos hrleft hrright hfit
  have hXtwo : 2 ≤ targetCutoff Q A := by
    have := Nat.cast_nonneg (α := ℝ) H
    linarith
  have htail := tail_smallness_next Q A (Z.card + 2) Clow cF
    (by omega) (by omega) hC hXtwo
    (by simpa only [Nat.cast_add, Nat.cast_ofNat] using hscale)
  refine ⟨{
    left := a
    right := b
    nondegenerate := hab
    nested := hsub
    length := hlen
    avoids := ?_
    source := ?_
    cutoff_increases := nextCutoff_gt Q A H hheight
    target := ?_
    tail := ?_ }⟩
  · intro x hx
    exact (havoid x hx).1
  · intro x hx
    have hxavoid := havoid x hx
    exact ⟨hxavoid.2.1, lt_of_lt_of_le hxavoid.2.2
      (fusionRadius_le_source_accuracy Q r.den A r.den_pos hden.le)⟩
  · intro x hx z k hHk hk
    have hxparent : x ∈ Icc l u := ⟨(hsub hx).1.le, (hsub hx).2.le⟩
    have hrparent : (r : ℝ) ∈ Icc l u :=
      ⟨by linarith only [hrleft, hinterval], by linarith only [hrright, hinterval]⟩
    have hclose : |x - (r : ℝ)| ≤ ((Q : ℝ) ^ A)⁻¹ :=
      le_trans (havoid x hx).2.2.le
        (fusionRadius_le_source_accuracy Q Q A (by omega) (by omega))
    have hkT : (k : ℝ) < targetCutoff Q A :=
      lt_of_lt_of_le (by exact_mod_cast hk) (nextCutoff_le_targetCutoff Q A)
    exact safeCenter_avoidance_of_deriv_bound f l u M Q A H r x hM hsafe
      hf hderiv hrparent hxparent hclose z k (by omega) hHk hkT
  · rw [hlen, div_div]
    simpa only [Nat.cast_add, Nat.cast_ofNat, mul_comm] using htail

/-- One successor step from the counting hypotheses on the middle third.
Qmin is arbitrary and can include the previous denominator-growth bound.
The forbidden set Z is fixed before choosing Q. -/
theorem successor_from_counting
    (f : ℝ → ℝ) (Z : Finset ℝ) (l u M Clow cF C : ℝ)
    (A H Qmin : ℕ)
    (hinterval : l < u) (hA : 0 < A) (hH : 2 ≤ H)
    (hM : 0 ≤ M) (hC : 0 ≤ Clow) (hcF : 0 < cF)
    (hf : ∀ y ∈ Icc l u, DifferentiableAt ℝ f y)
    (hderiv : ∀ y ∈ Icc l u, |deriv f y| ≤ M)
    (hsupply : HasSourceSupply (l + (u - l) / 3) (u - (u - l) / 3) cF)
    (hcount : HasUniformDangerBound f (l + (u - l) / 3)
      (u - (u - l) / 3) M Clow C A)
    (htail : Clow * ((H : ℝ) ^ 98)⁻¹ ≤ (cF / 4) * ((u - l) / 3)) :
    ∃ Q : ℕ, Qmin ≤ Q ∧ 2 ≤ Q ∧ ∃ r : ℚ,
      Q ≤ r.den ∧ r.den < 2 * Q ∧
      Nonempty (SuccessorInterval f Z l u Clow cF Q A H r) := by
  have hmid : l + (u - l) / 3 < u - (u - l) / 3 := by linarith
  obtain ⟨Qs, _hQs, hs⟩ := safe_center_of_counting_estimates f
    (l + (u - l) / 3) (u - (u - l) / 3) M cF Clow C A hmid hcF hsupply hcount
  obtain ⟨Q, hmin, htwo, hfit, hheight, hscale⟩ :=
    exists_large_fusion_scale A H (Z.card + 2) (max Qmin Qs)
      Clow cF ((u - l) / 3) hA hcF (by linarith)
  have htailmid : Clow * ((H : ℝ) ^ 98)⁻¹ ≤
      cF * ((u - (u - l) / 3) - (l + (u - l) / 3)) / 4 := by
    rw [middle_third_length]
    nlinarith [htail]
  obtain ⟨r, hrl, hru, hdenlo, hdenhi, hsafe⟩ :=
    hs H hH htailmid Q (by omega)
  refine ⟨Q, by omega, htwo, r, hdenlo, hdenhi, ?_⟩
  exact successor_from_safe_center f Z l u M Clow cF Q A H r
    hinterval htwo hH hM hC hf hderiv hrl hru hdenhi hsafe hfit hheight
    (by simpa only [Nat.cast_add, Nat.cast_ofNat] using hscale)

end MahlerLean
