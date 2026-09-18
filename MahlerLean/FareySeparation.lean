import MahlerLean.RationalBlocks
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
The separation and one-interval counting argument of Lemma 2.1.
Canonical rational denominators ensure distinct source fractions are
counted once. These are upper bounds, not the supply bound of Lemma 2.2.
-/

namespace MahlerLean

/-- Distinct rationals are separated by the reciprocal of the product
of their positive reduced denominators. -/
theorem rational_separation (r s : ℚ) (hrs : r ≠ s) :
    1 / ((r.den : ℝ) * (s.den : ℝ)) ≤ |(r : ℝ) - (s : ℝ)| := by
  have hr : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hs : (0 : ℝ) < s.den := by exact_mod_cast s.den_pos
  let N : ℤ := r.num * (s.den : ℤ) - s.num * (r.den : ℤ)
  have hN : N ≠ 0 := sub_ne_zero.mpr (fun h => hrs (Rat.eq_iff_mul_eq_mul.mpr h))
  have hNbound : (1 : ℝ) ≤ |(N : ℝ)| := by exact_mod_cast Int.one_le_abs hN
  have hdiff : (r : ℝ) - (s : ℝ) = (N : ℝ) / ((r.den : ℝ) * (s.den : ℝ)) := by
    rw [Rat.cast_def, Rat.cast_def]
    dsimp [N]
    push_cast
    field_simp
  rw [hdiff, abs_div, abs_of_pos (mul_pos hr hs)]
  exact div_le_div_of_nonneg_right hNbound (mul_pos hr hs).le

/-- The strict Farey spacing for denominators less than 2Q. The lower
bound Q on the denominators is not needed for this inequality. -/
theorem denominator_block_separation (Q : ℕ) (hQ : 0 < Q)
    (r s : ℚ) (hrs : r ≠ s) (hr : r.den < 2 * Q) (hs : s.den < 2 * Q) :
    1 / (4 * (Q : ℝ) ^ 2) < |(r : ℝ) - (s : ℝ)| := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hrpos : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hspos : (0 : ℝ) < s.den := by exact_mod_cast s.den_pos
  have hrlt : (r.den : ℝ) < 2 * (Q : ℝ) := by exact_mod_cast hr
  have hslt : (s.den : ℝ) < 2 * (Q : ℝ) := by exact_mod_cast hs
  have hprod : (r.den : ℝ) * (s.den : ℝ) < 4 * (Q : ℝ) ^ 2 := by
    nlinarith [mul_lt_mul_of_pos_right hrlt hspos,
      mul_lt_mul_of_pos_left hslt (show 0 < 2 * (Q : ℝ) by positivity)]
  exact lt_of_lt_of_le
    (one_div_lt_one_div_of_lt (mul_pos hrpos hspos) hprod) (rational_separation r s hrs)

/-- Packing bound for a finite family of real values separated by delta.
The floor map relative to l is injective into [0,floor((u-l)/delta)]. -/
theorem card_le_of_separated_values {α : Type*} (S : Finset α)
    (value : α → ℝ) (l u delta : ℝ) (hlu : l ≤ u) (hdelta : 0 < delta)
    (hmem : ∀ x ∈ S, l ≤ value x ∧ value x ≤ u)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → delta ≤ |value x - value y|) :
    (S.card : ℝ) ≤ (u - l) / delta + 1 := by
  classical
  let code (x : α) : ℕ := ⌊(value x - l) / delta⌋₊
  let N : ℕ := ⌊(u - l) / delta⌋₊
  have hmap : Set.MapsTo code (S : Set α) (Finset.Icc 0 N : Set ℕ) := by
    intro x hx
    apply Finset.mem_Icc.mpr
    exact ⟨Nat.zero_le _, Nat.floor_mono
      (div_le_div_of_nonneg_right (sub_le_sub_right (hmem x hx).2 l) hdelta.le)⟩
  have hinj : Set.InjOn code (S : Set α) := by
    intro x hx y hy hcode
    by_contra hxy
    have hxlo : (code x : ℝ) * delta ≤ value x - l :=
      (le_div_iff₀ hdelta).mp (Nat.floor_le (div_nonneg (sub_nonneg.mpr (hmem x hx).1) hdelta.le))
    have hylo : (code y : ℝ) * delta ≤ value y - l :=
      (le_div_iff₀ hdelta).mp (Nat.floor_le (div_nonneg (sub_nonneg.mpr (hmem y hy).1) hdelta.le))
    have hxhi : value x - l < ((code x : ℝ) + 1) * delta :=
      (div_lt_iff₀ hdelta).mp (Nat.lt_floor_add_one ((value x - l) / delta))
    have hyhi : value y - l < ((code y : ℝ) + 1) * delta :=
      (div_lt_iff₀ hdelta).mp (Nat.lt_floor_add_one ((value y - l) / delta))
    rw [hcode] at hxlo hxhi
    have hsmall : |value x - value y| < delta :=
      abs_lt.mpr ⟨by nlinarith, by nlinarith⟩
    exact (not_lt_of_ge (hsep x hx y hy hxy)) hsmall
  have hcard : S.card ≤ N + 1 := by
    simpa using Finset.card_le_card_of_injOn code hmap hinj
  have hcardR : (S.card : ℝ) ≤ (N : ℝ) + 1 := by exact_mod_cast hcard
  have hfloor : (N : ℝ) ≤ (u - l) / delta :=
    Nat.floor_le (div_nonneg (sub_nonneg.mpr hlu) hdelta.le)
  linarith

/-- An interval of length u-l contains at most 4Q^2(u-l)+1 members of
any finite set of distinct rationals with denominators less than 2Q. -/
theorem rational_interval_card_le (S : Finset ℚ) (l u : ℝ) (Q : ℕ)
    (hlu : l ≤ u) (hQ : 0 < Q)
    (hmem : ∀ r ∈ S, l ≤ (r : ℝ) ∧ (r : ℝ) ≤ u)
    (hden : ∀ r ∈ S, r.den < 2 * Q) :
    (S.card : ℝ) ≤ 4 * (Q : ℝ) ^ 2 * (u - l) + 1 := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have h := card_le_of_separated_values S (fun r : ℚ => (r : ℝ)) l u
    (1 / (4 * (Q : ℝ) ^ 2)) hlu (by positivity) hmem
    (fun r hr s hs hrs => (denominator_block_separation Q hQ r s hrs
      (hden r hr) (hden s hs)).le)
  simpa only [div_eq_mul_inv, one_mul, inv_inv, mul_comm] using h

/-- The one-interval upper bound for the exact source set used elsewhere
in the project. This does not imply its complementary lower bound. -/
theorem sourceFractions_card_le (l u : ℝ) (Q : ℕ) (hlu : l ≤ u) (hQ : 0 < Q) :
    ((sourceFractions l u Q).card : ℝ) ≤ 4 * (Q : ℝ) ^ 2 * (u - l) + 1 := by
  apply rational_interval_card_le (sourceFractions l u Q) l u Q hlu hQ
  · intro r hr
    have h := (mem_sourceFractions l u Q r).mp hr
    exact ⟨h.1, h.2.1⟩
  · intro r hr
    exact ((mem_sourceFractions l u Q r).mp hr).2.2.2

/-- A cell no longer than the Farey spacing contains at most one source
fraction, including the equality case because separation is strict. -/
theorem sourceFractions_card_le_one (l u : ℝ) (Q : ℕ) (hQ : 0 < Q)
    (hshort : u - l ≤ 1 / (4 * (Q : ℝ) ^ 2)) :
    (sourceFractions l u Q).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro r hr s hs
  by_contra hrs
  have hr' := (mem_sourceFractions l u Q r).mp hr
  have hs' := (mem_sourceFractions l u Q s).mp hs
  have hsep := denominator_block_separation Q hQ r s hrs hr'.2.2.2 hs'.2.2.2
  have habs : |(r : ℝ) - (s : ℝ)| ≤ u - l :=
    abs_le.mpr ⟨by linarith [hr'.1, hs'.2.1], by linarith [hr'.2.1, hs'.1]⟩
  linarith

end MahlerLean
