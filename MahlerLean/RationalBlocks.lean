import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Union
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Exact source and target sets for Sections 5 and 6 of paper/main.tex.
Source centers are rational numbers, so repeated representations are counted
once. The denominator restriction uses the canonical reduced denominator.
Target witnesses have arbitrary integer numerators and positive natural
number denominators; no coprimality is imposed on target witnesses.
-/

namespace MahlerLean

noncomputable section

/-- Reduced source rationals in `[l,u]` with denominator in `[Q,2Q)`.
The finite enumeration is filtered using the canonical denominator. -/
def sourceFractions (l u : ℝ) (Q : ℕ) : Finset ℚ := by
  classical
  exact ((Finset.Ico Q (2 * Q)).biUnion fun q =>
    (Finset.Icc ⌈l * (q : ℝ)⌉ ⌊u * (q : ℝ)⌋).image
      (fun p : ℤ => (p : ℚ) / (q : ℚ))).filter
    (fun r => Q ≤ r.den ∧ r.den < 2 * Q)

/-- The enumeration agrees exactly with the source set in the manuscript. -/
theorem mem_sourceFractions (l u : ℝ) (Q : ℕ) (r : ℚ) :
    r ∈ sourceFractions l u Q ↔
      l ≤ (r : ℝ) ∧ (r : ℝ) ≤ u ∧ Q ≤ r.den ∧ r.den < 2 * Q := by
  classical
  simp only [sourceFractions, Finset.mem_filter, Finset.mem_biUnion,
    Finset.mem_Ico, Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨q, hq, p, hp, rfl⟩, hden⟩
    have hqpos : (0 : ℝ) < q := by
      have : 0 < q := by omega
      exact_mod_cast this
    refine ⟨?_, ?_, hden⟩
    · simpa only [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast] using
        (le_div_iff₀ hqpos).2 (Int.ceil_le.mp hp.1)
    · simpa only [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast] using
        (div_le_iff₀ hqpos).2 (Int.le_floor.mp hp.2)
  · rintro ⟨hl, hu, hden⟩
    refine ⟨⟨r.den, hden, r.num, ⟨?_, ?_⟩, r.num_div_den⟩, hden⟩
    · apply Int.ceil_le.mpr
      exact (le_div_iff₀ (by exact_mod_cast r.den_pos : (0 : ℝ) < r.den)).mp
        (by simpa only [Rat.cast_def] using hl)
    · apply Int.le_floor.mpr
      exact (div_le_iff₀ (by exact_mod_cast r.den_pos : (0 : ℝ) < r.den)).mp
        (by simpa only [Rat.cast_def] using hu)

/-- The real upper target cutoff `T(Q,A) = Q^(A/97)`. -/
def targetCutoff (Q A : ℕ) : ℝ := (Q : ℝ) ^ ((A : ℝ) / 97)

/-- The margin `2 b^(-100) + 4 M Q^(-A)`, written with inverses of
natural powers to avoid ambiguity about integer versus real exponents. -/
def safetyMargin (M : ℝ) (Q A b : ℕ) : ℝ :=
  2 * ((b : ℝ) ^ 100)⁻¹ + 4 * M * ((Q : ℝ) ^ A)⁻¹

/-- A target witness. The explicit positivity condition excludes `b = 0`. -/
def HasTargetWitness (f : ℝ → ℝ) (M : ℝ) (Q A H : ℕ) (r : ℚ) : Prop :=
  ∃ a : ℤ, ∃ b : ℕ, 0 < b ∧ H ≤ b ∧ (b : ℝ) < targetCutoff Q A ∧
    |f (r : ℝ) - (a : ℝ) / (b : ℝ)| ≤ safetyMargin M Q A b

/-- The resonant source centers, counted once each even if they admit
several target witnesses. This is the set D(J;Q,A,H) in Section 5. -/
def dangerousSources (f : ℝ → ℝ) (l u M : ℝ) (Q A H : ℕ) : Finset ℚ := by
  classical
  exact (sourceFractions l u Q).filter (HasTargetWitness f M Q A H)

/-- The strict avoidance property in Lemma 6.1. -/
def IsSafeCenter (f : ℝ → ℝ) (M : ℝ) (Q A H : ℕ) (r : ℚ) : Prop :=
  ∀ a : ℤ, ∀ b : ℕ, 0 < b → H ≤ b → (b : ℝ) < targetCutoff Q A →
    safetyMargin M Q A b < |f (r : ℝ) - (a : ℝ) / (b : ℝ)|

/-- Negating the existential witness gives strict avoidance for all targets. -/
theorem isSafeCenter_iff_no_witness (f : ℝ → ℝ) (M : ℝ)
    (Q A H : ℕ) (r : ℚ) :
    IsSafeCenter f M Q A H r ↔ ¬ HasTargetWitness f M Q A H r := by
  constructor
  · intro hs hw
    obtain ⟨a, b, hb, hH, hT, hclose⟩ := hw
    exact (not_le_of_gt (hs a b hb hH hT)) hclose
  · intro hn a b hb hH hT
    exact lt_of_not_ge (fun hclose => hn ⟨a, b, hb, hH, hT, hclose⟩)

/-- A source center is safe exactly when it lies outside the dangerous set. -/
theorem isSafeCenter_iff_not_mem_dangerousSources
    (f : ℝ → ℝ) (l u M : ℝ) (Q A H : ℕ) (r : ℚ)
    (hr : r ∈ sourceFractions l u Q) :
    IsSafeCenter f M Q A H r ↔ r ∉ dangerousSources f l u M Q A H := by
  classical
  simp only [dangerousSources, Finset.mem_filter, hr, true_and]
  exact isSafeCenter_iff_no_witness f M Q A H r

end
end MahlerLean
