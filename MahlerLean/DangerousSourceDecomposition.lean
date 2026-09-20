import MahlerLean.SmallTargetDerivativeBounds
import Mathlib.Algebra.Order.Archimedean.Basic

namespace MahlerLean

/-- Locate every positive target height above H in a dyadic block. -/
theorem exists_dyadic_target_block {H y : ℝ} (hH : 0 < H) (hy : H ≤ y) :
    ∃ k : ℕ, (2 : ℝ)^k*H ≤ y ∧ y < 2*((2 : ℝ)^k*H) := by
  have hr : 1 ≤ y/H := (le_div_iff₀ hH).mpr (by simpa using hy)
  obtain ⟨k, hklo, hkhi⟩ := exists_nat_pow_near hr (by norm_num : (1 : ℝ) < 2)
  refine ⟨k, (le_div_iff₀ hH).mp hklo, ?_⟩
  have hh := (div_lt_iff₀ hH).mp hkhi
  rw [pow_succ] at hh
  nlinarith

def HasSmallTargetWitness (f : ℝ → ℝ) (M : ℝ) (Q A H : ℕ) (r : ℚ) : Prop :=
  ∃ k : ℕ, (2 : ℝ)^k*H < (Q : ℝ)^((1 : ℝ)/5) ∧
    ∃ p : ℤ, ∃ q : ℕ, 0 < q ∧ (2 : ℝ)^k*H ≤ (q : ℝ) ∧
      (q : ℝ) < 2*((2 : ℝ)^k*H) ∧ |f r-(p : ℝ)/q| ≤ safetyMargin M Q A q

def HasLargeTargetWitness (f : ℝ → ℝ) (M : ℝ) (Q A H : ℕ) (r : ℚ) : Prop :=
  ∃ k : ℕ, (Q : ℝ)^((1 : ℝ)/5) ≤ (2 : ℝ)^k*H ∧
    (2 : ℝ)^k*H < targetCutoff Q A ∧
    ∃ p : ℤ, ∃ q : ℕ, 0 < q ∧ (2 : ℝ)^k*H ≤ (q : ℝ) ∧
      (q : ℝ) < 2*((2 : ℝ)^k*H) ∧ |f r-(p : ℝ)/q| ≤ safetyMargin M Q A q

/-- An original witness belongs to the small or large regime according to
its block's left endpoint, including blocks crossing the transition. -/
theorem hasTargetWitness_small_or_large {f : ℝ → ℝ} {M : ℝ} {Q A H : ℕ} {r : ℚ}
    (hH : 0 < H) (hw : HasTargetWitness f M Q A H r) :
    HasSmallTargetWitness f M Q A H r ∨ HasLargeTargetWitness f M Q A H r := by
  obtain ⟨p,q,hq,hHq,hqT,herr⟩ := hw
  obtain ⟨k,hklo,hkhi⟩ := exists_dyadic_target_block
    (by exact_mod_cast hH : (0 : ℝ) < H) (by exact_mod_cast hHq : (H : ℝ) ≤ q)
  by_cases hk : (2 : ℝ)^k*H < (Q : ℝ)^((1 : ℝ)/5)
  · exact Or.inl ⟨k,hk,p,q,hq,hklo,hkhi,herr⟩
  · exact Or.inr ⟨k,le_of_not_gt hk,hklo.trans_lt hqT,p,q,hq,hklo,hkhi,herr⟩

end MahlerLean
