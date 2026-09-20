import MahlerLean.SmallTargetPacking

open Set
noncomputable section
namespace MahlerLean

def targetWitnessBox (B C : ℝ) : Finset (ℕ × ℤ) :=
  (Finset.range ⌈2*B⌉₊).product (Finset.Icc (-(⌈2*C*B⌉₊ : ℤ)) (⌈2*C*B⌉₊ : ℤ))

theorem mem_targetWitnessBox {B C : ℝ} {p : ℤ} {q : ℕ}
    (hC : 0 ≤ C) (hq : (q : ℝ) < 2*B) (hp : |(p : ℝ)| ≤ C*q) :
    (q,p) ∈ targetWitnessBox B C := by
  apply Finset.mem_product.mpr
  refine ⟨Finset.mem_range.mpr (Nat.lt_ceil.mpr hq), Finset.mem_Icc.mpr ?_⟩
  have hz : |(p : ℝ)| ≤ (⌈2*C*B⌉₊ : ℝ) :=
    (hp.trans (by nlinarith)).trans (Nat.le_ceil _)
  have hh := abs_le.mp hz
  change -(⌈2*C*B⌉₊ : ℤ) ≤ p ∧ p ≤ (⌈2*C*B⌉₊ : ℤ)
  constructor
  · exact_mod_cast hh.1
  · exact_mod_cast hh.2

theorem targetWitnessBox_card_le {B C : ℝ} (hB : 1 ≤ B) (hC : 0 ≤ C) :
    ((targetWitnessBox B C).card : ℝ) ≤ 3*(4*C+3)*B^2 := by
  have hB0 : 0 ≤ B := by linarith
  have hn := (Nat.ceil_lt_add_one (show 0 ≤ 2*B by positivity)).le
  have hz := (Nat.ceil_lt_add_one (show 0 ≤ 2*C*B by positivity)).le
  have hcard : (targetWitnessBox B C).card = ⌈2*B⌉₊ * (2*⌈2*C*B⌉₊+1) := by
    simp [targetWitnessBox, Int.card_Icc]
    omega
  rw [hcard, Nat.cast_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  have h1 : (⌈2*B⌉₊ : ℝ) ≤ 3*B := by linarith
  have h2 : 2*(⌈2*C*B⌉₊ : ℝ)+1 ≤ (4*C+3)*B := by nlinarith
  have hh := mul_le_mul h1 h2 (by positivity : 0 ≤ 2*(⌈2*C*B⌉₊ : ℝ)+1) (by positivity : 0 ≤ 3*B)
  nlinarith

end MahlerLean
