import MahlerLean.FareyCounting
import MahlerLean.CellCountingAssembly

open Set
noncomputable section
namespace MahlerLean

/-- Farey packing in one inverse image of a short target interval.
An inverse Lipschitz bound suffices; no disjoint-union decomposition is needed. -/
theorem rational_target_neighborhood_card_le
    (S : Finset ℚ) {f : ℝ → ℝ} {a b m y eps : ℝ} {Q : ℕ}
    (hm : 0 < m) (heps : 0 ≤ eps) (hQ : 0 < Q)
    (hinv : ∀ x ∈ Icc a b, ∀ z ∈ Icc a b, m * |x-z| ≤ |f x-f z|)
    (hx : ∀ r ∈ S, (r : ℝ) ∈ Icc a b)
    (herr : ∀ r ∈ S, |f r-y| ≤ eps)
    (hden : ∀ r ∈ S, r.den < 2*Q) :
    (S.card : ℝ) ≤ 4*(Q : ℝ)^2 * (2*eps/m) + 1 := by
  classical
  by_cases hS : S.Nonempty
  · let l := S.min' hS
    let u := S.max' hS
    have hl := S.min'_mem hS
    have hu := S.max'_mem hS
    have hlu : (l : ℝ) ≤ (u : ℝ) := by exact_mod_cast S.min'_le_max' hS
    have hlength : (u : ℝ)-(l : ℝ) ≤ 2*eps/m := by
      have hh := hinv u (hx _ hu) l (hx _ hl)
      have ht : |f u-f l| ≤ 2*eps := by
        have := abs_sub_le (f u) y (f l)
        rw [abs_sub_comm y (f l)] at this
        linarith [herr _ hu, herr _ hl]
      rw [abs_of_nonneg (sub_nonneg.mpr hlu)] at hh
      apply (le_div_iff₀ hm).mpr
      nlinarith
    have hc := rational_interval_card_le S l u Q hlu hQ
      (fun r hr ↦ ⟨by exact_mod_cast S.min'_le r hr,
        by exact_mod_cast S.le_max' r hr⟩) hden
    exact hc.trans (add_le_add_right (mul_le_mul_of_nonneg_left hlength (by positivity)) _)
  · have : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    rw [this]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

end MahlerLean
