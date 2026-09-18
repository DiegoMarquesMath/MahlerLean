import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleWith
import Mathlib.Tactic.NormNum

/-!
Compatibility with the manuscript's definition of a Liouville number,
and the two pointwise conclusions needed at the end of fusion.
-/

namespace MahlerLean

open Filter Set

/-- The manuscript's convention: for every positive integer exponent,
infinitely many pairs have denominator at least two and strictly positive
approximation error below the reciprocal power. Positive denominators
are represented by natural numbers. -/
def PaperLiouville (x : ℝ) : Prop :=
  ∀ N : ℕ, 1 ≤ N →
    {ab : ℤ × ℕ | 2 ≤ ab.2 ∧
      0 < |x - (ab.1 : ℝ) / (ab.2 : ℝ)| ∧
      |x - (ab.1 : ℝ) / (ab.2 : ℝ)| < ((ab.2 : ℝ) ^ N)⁻¹}.Infinite

/-- The library definition and the manuscript's infinitely-many-pairs
convention agree. Neither direction drops the nonzero-error condition. -/
theorem liouville_iff_paperLiouville (x : ℝ) : Liouville x ↔ PaperLiouville x := by
  constructor
  · intro hx N _hN
    apply Set.Infinite.of_image Prod.snd
    apply Set.infinite_of_not_bddAbove
    rintro ⟨B, hB⟩
    obtain ⟨b, hb, a, hne, happrox⟩ :=
      frequently_atTop.mp (hx.frequently_exists_num N) (max 2 (B + 1))
    have hpair : (a, b) ∈ {ab : ℤ × ℕ | 2 ≤ ab.2 ∧
        0 < |x - (ab.1 : ℝ) / (ab.2 : ℝ)| ∧
        |x - (ab.1 : ℝ) / (ab.2 : ℝ)| < ((ab.2 : ℝ) ^ N)⁻¹} := by
      exact ⟨by omega, abs_pos.mpr (sub_ne_zero.mpr hne), by simpa [one_div] using happrox⟩
    have hbound : b ≤ B := hB ⟨(a, b), hpair, rfl⟩
    omega
  · intro hx N
    obtain ⟨⟨a, b⟩, hb, hpos, happrox⟩ := (hx (N + 1) (by omega)).nonempty
    have hbpos : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
    have hbone : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
    have hmono : 1 / (b : ℝ) ^ (N + 1) ≤ 1 / (b : ℝ) ^ N := by
      apply one_div_le_one_div_of_le (pow_pos hbpos N)
      exact pow_le_pow_right₀ hbone (Nat.le_succ N)
    refine ⟨a, (b : ℤ), by exact_mod_cast (show 1 < b by omega), ?_, ?_⟩
    · simpa only [Int.cast_natCast] using sub_ne_zero.mp (abs_pos.mp hpos)
    · simpa only [Int.cast_natCast] using
        lt_of_lt_of_le (by simpa only [one_div] using happrox) hmono

/-- The source approximation invariant with orders A_n = n + 3 implies
that the point is Liouville. The centers use canonical reduced fractions. -/
theorem liouville_of_source_approximations
    (x : ℝ) (r : ℕ → ℚ)
    (hden : ∀ n, 2 ≤ (r n).den)
    (happrox : ∀ n, 0 < |x - (r n : ℝ)| ∧
      |x - (r n : ℝ)| < (((r n).den : ℝ) ^ (n + 3))⁻¹) :
    Liouville x := by
  intro N
  have hbpos : (0 : ℝ) < (r N).den := by exact_mod_cast (r N).den_pos
  have hbone : (1 : ℝ) ≤ (r N).den := by
    exact_mod_cast (show 1 ≤ (r N).den by have := hden N; omega)
  have hmono : 1 / ((r N).den : ℝ) ^ (N + 3) ≤
      1 / ((r N).den : ℝ) ^ N := by
    apply one_div_le_one_div_of_le (pow_pos hbpos N)
    exact pow_le_pow_right₀ hbone (by omega)
  refine ⟨(r N).num, ((r N).den : ℤ), ?_, ?_, ?_⟩
  · exact_mod_cast (show 1 < (r N).den by have := hden N; omega)
  · have hne := sub_ne_zero.mp (abs_pos.mp (happrox N).1)
    simpa only [Rat.cast_def, Int.cast_natCast] using hne
  · have hlt : |x - (r N : ℝ)| < 1 / ((r N).den : ℝ) ^ N :=
      lt_of_lt_of_le (by simpa only [one_div] using (happrox N).2) hmono
    simpa only [Rat.cast_def, Int.cast_natCast] using hlt

/-- The explicit eventual lower bound in Theorem 1.2, at a natural
exponent tau and a lower denominator cutoff B. -/
def EventualTargetAvoidance (y : ℝ) (tau B : ℕ) : Prop :=
  ∀ a : ℤ, ∀ b : ℕ, B ≤ b →
    ((b : ℝ) ^ tau)⁻¹ < |y - (a : ℝ) / (b : ℝ)|

/-- A fixed eventual lower bound for rational approximation excludes
the Liouville property. -/
theorem not_liouville_of_eventual_target_avoidance
    (y : ℝ) (tau B : ℕ) (havoid : EventualTargetAvoidance y tau B) :
    ¬ Liouville y := by
  intro hy
  obtain ⟨b, hb, a, _hne, happrox⟩ :=
    frequently_atTop.mp (hy.frequently_exists_num tau) (max 2 B)
  have hsafe := havoid a b (by omega)
  have hsmall : |y - (a : ℝ) / (b : ℝ)| < ((b : ℝ) ^ tau)⁻¹ := by
    simpa only [one_div] using happrox
  exact (not_lt_of_ge hsafe.le) hsmall

end MahlerLean
