import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
Quantitative interval selection after deleting finitely many real points.
The proof uses separated closed intervals of equal length and the
pigeonhole principle. It gives the same length needed in Section 6 without
formalizing connected components of the complement of a finite set.
-/

namespace MahlerLean

open Set

/-- If fewer than N points are forbidden, an open interval (a,b) contains
a closed interval of length (b-a)/(2N) avoiding all forbidden points. -/
theorem exists_interval_avoiding_finset
    (F : Finset ℝ) (a b : ℝ) (N : ℕ) (hab : a < b) (hcard : F.card < N) :
    ∃ l u : ℝ, a < l ∧ l < u ∧ u < b ∧
      u - l = (b - a) / (2 * (N : ℝ)) ∧
      ∀ x ∈ Icc l u, x ∉ F := by
  classical
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let s : ℝ := (b - a) / (2 * (N : ℝ))
  have hs : 0 < s := div_pos (sub_pos.mpr hab) (by positivity)
  have hscale : s * (2 * (N : ℝ)) = b - a := div_mul_cancel₀ _ (by positivity)
  let lo (i : Fin N) : ℝ := a + (2 * (i.val : ℝ) + 1 / 2) * s
  let hi (i : Fin N) : ℝ := a + (2 * (i.val : ℝ) + 3 / 2) * s
  have hwidth (i : Fin N) : hi i - lo i = s := by dsimp [hi, lo]; ring
  have hgeom (i : Fin N) : a < lo i ∧ lo i < hi i ∧ hi i < b := by
    have hiN : (i.val : ℝ) + 1 ≤ N := by exact_mod_cast (Nat.succ_le_iff.mpr i.isLt)
    have hcoef : 2 * (i.val : ℝ) + 3 / 2 < 2 * (N : ℝ) := by linarith
    have hmul := mul_lt_mul_of_pos_right hcoef hs
    have hstart : 0 < (2 * (i.val : ℝ) + 1 / 2) * s := by positivity
    have hw := hwidth i
    dsimp [lo, hi] at *
    exact ⟨by linarith, by linarith, by nlinarith⟩
  have hsep (i j : Fin N) (hij : i.val < j.val) : hi i < lo j := by
    have hijR : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast (Nat.succ_le_iff.mpr hij)
    have hcoef : 2 * (i.val : ℝ) + 3 / 2 < 2 * (j.val : ℝ) + 1 / 2 := by linarith
    exact add_lt_add_left (mul_lt_mul_of_pos_right hcoef hs) a
  have hfree : ∃ i : Fin N, ∀ x ∈ Icc (lo i) (hi i), x ∉ F := by
    by_contra hn
    push_neg at hn
    choose w hwI hwF using hn
    let wf : Fin N → {x : ℝ // x ∈ F} := fun i => ⟨w i, hwF i⟩
    have hinj : Function.Injective wf := by
      intro i j hij
      have heq : w i = w j := congrArg Subtype.val hij
      apply Fin.ext
      rcases lt_trichotomy i.val j.val with hlt | hequal | hgt
      · have hsij := hsep i j hlt
        have hwi := hwI i
        have hwj := hwI j
        linarith [hwi.2, hwj.1]
      · exact hequal
      · have hsji := hsep j i hgt
        have hwi := hwI i
        have hwj := hwI j
        linarith [hwj.2, hwi.1]
    have hle : N ≤ F.card := by simpa using Fintype.card_le_of_injective wf hinj
    omega
  obtain ⟨i, havoid⟩ := hfree
  exact ⟨lo i, hi i, (hgeom i).1, (hgeom i).2.1, (hgeom i).2.2, hwidth i, havoid⟩

/-- The interval size used in fusion, with Lambda = #Z + 2.
The forbidden set includes both Z and the current center r. -/
theorem exists_interval_avoiding_zeros_and_center
    (Z : Finset ℝ) (r R : ℝ) (hR : 0 < R) :
    ∃ l u : ℝ, l < u ∧ Icc l u ⊆ Ioo (r - R) (r + R) ∧
      u - l = R / ((Z.card : ℝ) + 2) ∧
      ∀ x ∈ Icc l u, x ∉ Z ∧ 0 < |x - r| ∧ |x - r| < R := by
  classical
  have hcard : (insert r Z).card < Z.card + 2 := by
    have := Finset.card_insert_le r Z
    omega
  obtain ⟨l, u, hl, hlu, hu, hlen, havoid⟩ :=
    exists_interval_avoiding_finset (insert r Z) (r - R) (r + R)
      (Z.card + 2) (by linarith) hcard
  have hsub : Icc l u ⊆ Ioo (r - R) (r + R) := by
    intro x hx
    exact ⟨lt_of_lt_of_le hl hx.1, lt_of_le_of_lt hx.2 hu⟩
  refine ⟨l, u, hlu, hsub, ?_, ?_⟩
  · rw [hlen]
    push_cast
    field_simp
    ring
  · intro x hx
    have hnot := havoid x hx
    simp only [Finset.mem_insert, not_or] at hnot
    have hxin := hsub hx
    exact ⟨hnot.2, abs_pos.mpr (sub_ne_zero.mpr hnot.1),
      abs_lt.mpr ⟨by linarith [hxin.1], by linarith [hxin.2]⟩⟩

/-- The chosen interval also lies inside the previous parent interval
when the center is in its middle third and the radius fits the margin. -/
theorem exists_next_interval_in_parent
    (Z : Finset ℝ) (l u r R : ℝ) (hR : 0 < R)
    (hleft : l + (u - l) / 3 ≤ r) (hright : r ≤ u - (u - l) / 3)
    (hfit : R < (u - l) / 3) :
    ∃ a b : ℝ, a < b ∧ Icc a b ⊆ Ioo l u ∧
      b - a = R / ((Z.card : ℝ) + 2) ∧
      ∀ x ∈ Icc a b, x ∉ Z ∧ 0 < |x - r| ∧ |x - r| < R := by
  obtain ⟨a, b, hab, hsub, hlen, havoid⟩ :=
    exists_interval_avoiding_zeros_and_center Z r R hR
  refine ⟨a, b, hab, ?_, hlen, havoid⟩
  intro x hx
  have hxball := hsub hx
  exact ⟨by linarith [hxball.1], by linarith [hxball.2]⟩

/-- Exact length of the middle third of a closed interval. -/
theorem middle_third_length (a b : ℝ) :
    (b - (b - a) / 3) - (a + (b - a) / 3) = (b - a) / 3 := by
  ring

end MahlerLean
