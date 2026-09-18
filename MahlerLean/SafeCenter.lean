import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
Small supporting lemmas for Section 6.
Neither the counting estimate nor the existence of a Liouville escape point
is asserted in this file.
-/

namespace MahlerLean

/-- A smaller forbidden set cannot exhaust a finite supply of centers. -/
theorem exists_safe_center {α : Type*} [DecidableEq α]
    (S D : Finset α) (hcard : D.card < S.card) :
    ∃ r ∈ S, r ∉ D := by
  classical
  by_contra hn
  have hsub : S ⊆ D := by
    intro r hr
    by_contra hd
    exact hn ⟨r, hr, hd⟩
  exact (not_lt_of_ge (Finset.card_le_card hsub)) hcard

/-- The numerical budget in Lemma 6.1. -/
theorem counting_budget (supply main remainder : ℝ)
    (hpos : 0 < supply)
    (hmain : main ≤ supply / 4)
    (hrem : remainder ≤ supply / 4) :
    main + remainder < supply := by
  linarith

/-- Abstract form of (6.19)--(6.20).
Here u = f(r), v = f(x), a is a target rational,
epsilon = b^(-100), and delta = M_* Q^(-A).
-/
theorem safety_transfer (u v a epsilon delta : ℝ)
    (hepsilon : 0 ≤ epsilon) (hdelta : 0 ≤ delta)
    (hcenter : 2 * epsilon + 4 * delta < |u - a|)
    (hmove : |v - u| ≤ delta) :
    epsilon < |v - a| := by
  have htriangle : |u - a| ≤ delta + |v - a| := calc
    |u - a| ≤ |u - v| + |v - a| := abs_sub_le u v a
    _ = |v - u| + |v - a| := by rw [abs_sub_comm u v]
    _ ≤ delta + |v - a| := add_le_add_right hmove _
  linarith

end MahlerLean
