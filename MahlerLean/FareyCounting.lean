import MahlerLean.FareySeparation
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.Finset.Max

/-!
The finite-union upper estimate of Lemma 2.1, stated for an explicitly
given disjoint interval decomposition. OrdConnected allows open, closed,
half-open and degenerate intervals. Extended-real volume also covers
unbounded intervals; the real-valued corollary assumes finite volume.

No source-supply estimate or analytic sublevel estimate is assumed here.
Producing the interval decomposition of an analytic sublevel set remains
a task for the later analytic part of the project.
-/

namespace MahlerLean

open Set MeasureTheory
open scoped ENNReal

/-- An order-connected set contains the closed span of any finite subset.
Farey packing on that span gives the upper bound in terms of its volume. -/
theorem rational_ordConnected_card_le_volume (S : Finset ℚ) (E : Set ℝ)
    (Q : ℕ) (hQ : 0 < Q) (hE : OrdConnected E)
    (hmem : ∀ r ∈ S, (r : ℝ) ∈ E) (hden : ∀ r ∈ S, r.den < 2 * Q) :
    (S.card : ℝ≥0∞) ≤ ENNReal.ofReal (4 * (Q : ℝ) ^ 2) * volume E + 1 := by
  classical
  by_cases hS : S.Nonempty
  · let a : ℝ := (S.min' hS : ℚ)
    let b : ℝ := (S.max' hS : ℚ)
    have hab : a ≤ b := by dsimp [a, b]; exact_mod_cast S.min'_le_max' hS
    have hK : 0 ≤ 4 * (Q : ℝ) ^ 2 := by positivity
    have hwidth : 0 ≤ b - a := sub_nonneg.mpr hab
    have hproduct : 0 ≤ 4 * (Q : ℝ) ^ 2 * (b - a) := mul_nonneg hK hwidth
    have hinside : ∀ r ∈ S, a ≤ (r : ℝ) ∧ (r : ℝ) ≤ b := by
      intro r hr
      exact ⟨by dsimp [a]; exact_mod_cast S.min'_le r hr,
        by dsimp [b]; exact_mod_cast S.le_max' r hr⟩
    have hcard := rational_interval_card_le S a b Q hab hQ hinside hden
    have hcast : (S.card : ℝ≥0∞) ≤
        ENNReal.ofReal (4 * (Q : ℝ) ^ 2) * ENNReal.ofReal (b - a) + 1 := by
      have := ENNReal.ofReal_le_ofReal hcard
      simpa only [ENNReal.ofReal_natCast,
        ENNReal.ofReal_add hproduct (by norm_num : (0 : ℝ) ≤ 1),
        ENNReal.ofReal_mul hK, ENNReal.ofReal_one] using this
    have hspan : Icc a b ⊆ E := hE.out (hmem _ (S.min'_mem hS)) (hmem _ (S.max'_mem hS))
    have hvol : ENNReal.ofReal (b - a) ≤ volume E := by
      simpa only [Real.volume_Icc] using (measure_mono hspan : volume (Icc a b) ≤ volume E)
    exact hcast.trans (add_le_add_right (mul_le_mul_left' hvol _) 1)
  · have hzero : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp only [hzero, Finset.card_empty, Nat.cast_zero]
    exact bot_le

/-- The upper bound on a finite disjoint union of intervals. The additive
term is the number of supplied components, with no extra factor Q. -/
theorem rational_union_card_le_volume {ι : Type*} (t : Finset ι)
    (E : ι → Set ℝ) (S : Finset ℚ) (Q : ℕ) (hQ : 0 < Q)
    (hintervals : ∀ i ∈ t, OrdConnected (E i))
    (hdisjoint : Set.PairwiseDisjoint (t : Set ι) E)
    (hcover : ∀ r ∈ S, ∃ i ∈ t, (r : ℝ) ∈ E i)
    (hden : ∀ r ∈ S, r.den < 2 * Q) :
    (S.card : ℝ≥0∞) ≤
      ENNReal.ofReal (4 * (Q : ℝ) ^ 2) * volume (⋃ i ∈ t, E i) + t.card := by
  classical
  let parts (i : ι) : Finset ℚ := S.filter (fun r => (r : ℝ) ∈ E i)
  have hdecomp : S = t.biUnion parts := by
    ext r
    simp only [Finset.mem_biUnion, parts, Finset.mem_filter]
    constructor
    · intro hr
      obtain ⟨i, hi, hri⟩ := hcover r hr
      exact ⟨i, hi, hr, hri⟩
    · rintro ⟨i, _hi, hr, _hri⟩
      exact hr
  have hcard : (S.card : ℝ≥0∞) ≤ ∑ i ∈ t, ((parts i).card : ℝ≥0∞) := by
    rw [hdecomp]
    exact_mod_cast (Finset.card_biUnion_le (s := t) (t := parts))
  have hparts : ∀ i ∈ t, ((parts i).card : ℝ≥0∞) ≤
      ENNReal.ofReal (4 * (Q : ℝ) ^ 2) * volume (E i) + 1 := by
    intro i hi
    apply rational_ordConnected_card_le_volume (parts i) (E i) Q hQ (hintervals i hi)
    · intro r hr
      exact (Finset.mem_filter.mp hr).2
    · intro r hr
      exact hden r (Finset.mem_filter.mp hr).1
  have hvol : volume (⋃ i ∈ t, E i) = ∑ i ∈ t, volume (E i) :=
    measure_biUnion_finset hdisjoint (fun i hi => (hintervals i hi).measurableSet)
  calc
    (S.card : ℝ≥0∞) ≤ ∑ i ∈ t, ((parts i).card : ℝ≥0∞) := hcard
    _ ≤ ∑ i ∈ t, (ENNReal.ofReal (4 * (Q : ℝ) ^ 2) * volume (E i) + 1) :=
      Finset.sum_le_sum hparts
    _ = ENNReal.ofReal (4 * (Q : ℝ) ^ 2) * volume (⋃ i ∈ t, E i) + t.card := by
      rw [hvol, Finset.sum_add_distrib, ← Finset.mul_sum]
      simp

/-- Real-valued form of Lemma 2.1 for a finite-volume set supplied as at
most R pairwise disjoint intervals. This is the component form used in
the manuscript proof. A decomposition is an explicit input. -/
theorem rational_union_card_le {ι : Type*} (t : Finset ι)
    (E : ι → Set ℝ) (S : Finset ℚ) (Q R : ℕ) (hQ : 0 < Q)
    (hR : t.card ≤ R) (hintervals : ∀ i ∈ t, OrdConnected (E i))
    (hdisjoint : Set.PairwiseDisjoint (t : Set ι) E)
    (hcover : ∀ r ∈ S, ∃ i ∈ t, (r : ℝ) ∈ E i)
    (hden : ∀ r ∈ S, r.den < 2 * Q)
    (hfinite : volume (⋃ i ∈ t, E i) ≠ ∞) :
    (S.card : ℝ) ≤ 4 * (Q : ℝ) ^ 2 * (volume (⋃ i ∈ t, E i)).toReal + R := by
  have hbound := rational_union_card_le_volume t E S Q hQ hintervals hdisjoint hcover hden
  have hrhs : ENNReal.ofReal (4 * (Q : ℝ) ^ 2) * volume (⋃ i ∈ t, E i) + t.card ≠ ∞ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite, by simp⟩
  have hreal := ENNReal.toReal_mono hrhs hbound
  have hK : 0 ≤ 4 * (Q : ℝ) ^ 2 := by positivity
  have hcastfinite : (t.card : ℝ≥0∞) ≠ ∞ := by simp
  have hcard : (S.card : ℝ) ≤
      4 * (Q : ℝ) ^ 2 * (volume (⋃ i ∈ t, E i)).toReal + t.card := by
    simpa only [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite)
        hcastfinite, ENNReal.toReal_natCast, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hK] using hreal
  have hRreal : (t.card : ℝ) ≤ R := by exact_mod_cast hR
  linarith

end MahlerLean
