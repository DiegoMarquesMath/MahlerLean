import MahlerLean.RationalWronskianNonvanishing
import Mathlib.Data.EReal.Basic

/-! The manuscript's irrationality exponent: positive real exponents with
infinitely many integer numerator/positive natural denominator pairs.
Fractions need not be reduced, and zero approximation error is excluded. -/
noncomputable section
open Set
namespace MahlerLean

/-- The rational approximation pairs used in the manuscript’s definition of μ. -/
def approximationPairs (y lam : ℝ) : Set (ℤ × ℕ) :=
  {p | 0 < p.2 ∧ 0 < |y - (p.1 : ℝ) / (p.2 : ℝ)| ∧
    |y - (p.1 : ℝ) / (p.2 : ℝ)| < (p.2 : ℝ) ^ (-lam)}

/-- Extended-real supremum, allowing irrationality exponent +∞. -/
def irrationalityExponent (y : ℝ) : EReal :=
  sSup ((fun lam : ℝ ↦ (lam : EReal)) ''
    {lam : ℝ | 0 < lam ∧ (approximationPairs y lam).Infinite})

/-- An eventual power lower bound leaves finitely many approximation pairs
at every larger exponent, including all possible small denominators. -/
theorem approximationPairs_finite_of_eventual_target_avoidance
    {y : ℝ} {tau B : ℕ} (havoid : EventualTargetAvoidance y tau B)
    {lam : ℝ} (hlam : (tau : ℝ) < lam) : (approximationPairs y lam).Finite := by
  let C : ℤ := ⌈(B : ℝ) * (|y| + 1)⌉
  apply ((Set.finite_Icc (-C) C).prod (Set.finite_Iio B)).subset
  rintro ⟨a,b⟩ ⟨hb, _herr, happrox⟩
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hbpos : (0 : ℝ) < b := by positivity
  have hpow : (b : ℝ)^(-lam) ≤ ((b : ℝ)^tau)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg (by positivity)]
    exact Real.rpow_le_rpow_of_exponent_le hb1 (by linarith)
  have hbB : b < B := by
    by_contra h
    have hs := havoid a b (by omega)
    exact (not_lt_of_ge hs.le) (happrox.trans_le hpow)
  have hlampos : 0 < lam := lt_of_le_of_lt (Nat.cast_nonneg tau) hlam
  have hp1 : (b : ℝ)^(-lam) ≤ 1 := by
    calc (b : ℝ)^(-lam) ≤ (b : ℝ)^(0 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hb1 (by linarith)
      _ = 1 := Real.rpow_zero _
  have he : |y - (a : ℝ)/(b : ℝ)| < 1 := happrox.trans_le hp1
  have ha : |(a : ℝ)| < (b : ℝ) * (|y| + 1) := by
    have ht := abs_add_le ((a : ℝ)/(b : ℝ)-y) y
    rw [sub_add_cancel, abs_sub_comm, abs_div, abs_of_pos hbpos] at ht
    have hd : |(a : ℝ)| / (b : ℝ) < |y| + 1 := by linarith
    exact (div_lt_iff₀ hbpos).mp hd |>.trans_le (by ring_nf; rfl)
  have hbB' : (b : ℝ) ≤ B := by exact_mod_cast hbB.le
  have haC : |(a : ℝ)| ≤ (C : ℝ) :=
    ha.le.trans ((mul_le_mul_of_nonneg_right hbB' (by positivity)).trans (Int.le_ceil _))
  have habounds := abs_le.mp haC
  refine ⟨⟨?_, ?_⟩, hbB⟩
  · exact_mod_cast habounds.1
  · exact_mod_cast habounds.2

/-- The eventual approximation bound implies the bound for the manuscript's μ. -/
theorem irrationalityExponent_le_of_eventual_target_avoidance
    {y : ℝ} {tau B : ℕ} (havoid : EventualTargetAvoidance y tau B) :
    irrationalityExponent y ≤ ((tau : ℝ) : EReal) := by
  apply sSup_le
  rintro t ⟨lam, ⟨_hpos, hinf⟩, rfl⟩
  apply EReal.coe_le_coe_iff.mpr
  by_contra hn
  exact hinf (approximationPairs_finite_of_eventual_target_avoidance havoid (lt_of_not_ge hn))

/-- The local quantitative theorem, including its explicit eventual lower bound. -/
theorem theorem_1_2
    {f : ℝ → ℝ} {U V : Set ℝ} (hU : IsOpen U) (hconn : IsPreconnected U)
    (hf : AnalyticOnNhd ℝ f U) (hnr : ¬ IsRationalOn f U)
    (hV : IsOpen V) (hne : V.Nonempty) (hVU : V ⊆ U) :
    ∃ ξ : ℝ, ξ ∈ V ∧ Liouville ξ ∧ irrationalityExponent (f ξ) ≤ (100 : EReal) ∧
      ∃ B : ℕ, 2 ≤ B ∧ EventualTargetAvoidance (f ξ) 100 B := by
  obtain ⟨ξ, B, hξ, hB, hL, _hPL, havoid, _hnL⟩ :=
    exists_escape_of_analytic_not_rational hU hconn hf hnr hV hne hVU
  refine ⟨ξ, hξ, hL, ?_, B, hB, havoid⟩
  simpa using irrationalityExponent_le_of_eventual_target_avoidance havoid

end MahlerLean
