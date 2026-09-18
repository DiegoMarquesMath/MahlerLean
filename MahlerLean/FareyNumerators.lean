import MahlerLean.FareySeparation
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Data.Nat.Totient

/-!
Finite arithmetic for the proof of Lemma 2.2. Numerators may be negative
or zero. The discrepancy estimates have absolute constants, independent
of the location and length of the interval. The eventual quadratic lower
bound still requires a separate summation argument.
-/

namespace MahlerLean

noncomputable section
open Finset

/-- Integer numerators of reduced fractions in `[l,u]` at denominator q. -/
def reducedNumerators (l u : ℝ) (q : ℕ) : Finset ℤ :=
  (Icc ⌈l * (q : ℝ)⌉ ⌊u * (q : ℝ)⌋).filter (fun p => p.natAbs.Coprime q)

/-- Membership uses the exact coprimality convention for signed numerators. -/
theorem mem_reducedNumerators (l u : ℝ) (q : ℕ) (p : ℤ) :
    p ∈ reducedNumerators l u q ↔
      l * (q : ℝ) ≤ p ∧ (p : ℝ) ≤ u * q ∧ p.natAbs.Coprime q := by
  simp only [reducedNumerators, mem_filter, mem_Icc, Int.ceil_le, Int.le_floor]
  tauto

/-- The integer count in any nonempty real interval differs from its
length by at most one, including either integer endpoint. -/
theorem integer_interval_card_discrepancy (a b : ℝ) (hab : a ≤ b) :
    |((Icc ⌈a⌉ ⌊b⌋).card : ℝ) - (b - a)| ≤ 1 := by
  have hceil := Int.ceil_lt_add_one a
  have hfloor := Int.lt_floor_add_one b
  have hle : ⌈a⌉ ≤ ⌊b⌋ + 1 := by
    have : (⌈a⌉ : ℝ) < (⌊b⌋ : ℝ) + 2 := by linarith
    have : ⌈a⌉ < ⌊b⌋ + 2 := by exact_mod_cast this
    omega
  have hc : ((Icc ⌈a⌉ ⌊b⌋).card : ℝ) = (⌊b⌋ : ℝ) + 1 - (⌈a⌉ : ℝ) := by
    exact_mod_cast Int.card_Icc_of_le _ _ hle
  rw [hc, abs_le]
  constructor <;> linarith [Int.floor_le b, Int.le_ceil a]

/-- Restricting integer numerators to multiples of d amounts to rescaling
the endpoints. This identity is valid on intervals crossing zero. -/
theorem multiples_interval_card (a b : ℝ) (d : ℕ) (hd : 0 < d) :
    ((Icc ⌈a⌉ ⌊b⌋).filter (fun p : ℤ => (d : ℤ) ∣ p)).card =
      (Icc ⌈a / d⌉ ⌊b / d⌋).card := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hdZ : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
  symm
  apply card_bij (fun k _ => (d : ℤ) * k)
  · intro k hk
    simp only [mem_Icc, Int.ceil_le, Int.le_floor] at hk
    simp only [mem_filter, mem_Icc, Int.ceil_le, Int.le_floor]
    push_cast
    exact ⟨⟨by nlinarith [(div_le_iff₀ hdR).mp hk.1],
      by nlinarith [(le_div_iff₀ hdR).mp hk.2]⟩, dvd_mul_right _ _⟩
  · intro k _ j _ h
    exact mul_left_cancel₀ hdZ h
  · intro p hp
    simp only [mem_filter, mem_Icc, Int.ceil_le, Int.le_floor] at hp
    obtain ⟨k, rfl⟩ := hp.2
    refine ⟨k, ?_, rfl⟩
    simp only [mem_Icc, Int.ceil_le, Int.le_floor]
    push_cast at hp
    constructor
    · apply (div_le_iff₀ hdR).mpr
      nlinarith [hp.1.1]
    · apply (le_div_iff₀ hdR).mpr
      nlinarith [hp.1.2]

/-- An absolute error of one for the count of multiples of d. -/
theorem multiples_interval_discrepancy (a b : ℝ) (hab : a ≤ b)
    (d : ℕ) (hd : 0 < d) :
    |(((Icc ⌈a⌉ ⌊b⌋).filter (fun p : ℤ => (d : ℤ) ∣ p)).card : ℝ) -
      (b - a) / d| ≤ 1 := by
  rw [multiples_interval_card a b d hd, sub_div]
  exact integer_interval_card_discrepancy _ _
    (div_le_div_of_nonneg_right hab (by positivity))

/-- Möbius inversion expresses coprimality as a sum over common divisors.
The positive denominator excludes the exceptional gcd(0,0). -/
theorem coprime_indicator_moebius (p : ℤ) (q : ℕ) (hq : 0 < q) :
    (if p.natAbs.Coprime q then (1 : ℝ) else 0) =
      ∑ d ∈ q.divisors, if (d : ℤ) ∣ p then
        (ArithmeticFunction.moebius d : ℝ) else 0 := by
  have hg : p.natAbs.gcd q ≠ 0 := by
    intro h
    exact hq.ne' (Nat.gcd_eq_zero_iff.mp h).2
  have hfilter : q.divisors.filter (fun d : ℕ => (d : ℤ) ∣ p) =
      (p.natAbs.gcd q).divisors := by
    ext d
    simp only [mem_filter, Nat.mem_divisors, Int.natCast_dvd,
      Nat.dvd_gcd_iff]
    have hq0 : q ≠ 0 := hq.ne'
    tauto
  rw [← sum_filter, hfilter]
  have hs : (∑ d ∈ (p.natAbs.gcd q).divisors,
      ArithmeticFunction.moebius d) =
      if p.natAbs.gcd q = 1 then (1 : ℤ) else 0 := by
    rw [← ArithmeticFunction.coe_mul_zeta_apply,
      ArithmeticFunction.moebius_mul_coe_zeta, ArithmeticFunction.one_apply]
  have hsR := congrArg (fun z : ℤ => (z : ℝ)) hs
  push_cast at hsR
  simpa only [Nat.Coprime] using hsR.symm

/-- Exact finite Möbius formula for the number of coprime numerators. -/
theorem reducedNumerators_card_moebius (l u : ℝ) (q : ℕ) (hq : 0 < q) :
    ((reducedNumerators l u q).card : ℝ) =
      ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ) *
        ((Icc ⌈l * q / d⌉ ⌊u * q / d⌋).card : ℝ) := by
  classical
  calc
    ((reducedNumerators l u q).card : ℝ) =
        ∑ p ∈ Icc ⌈l * q⌉ ⌊u * q⌋,
          if p.natAbs.Coprime q then (1 : ℝ) else 0 := by
      simp [reducedNumerators]
    _ = ∑ p ∈ Icc ⌈l * q⌉ ⌊u * q⌋,
        ∑ d ∈ q.divisors, if (d : ℤ) ∣ p then
          (ArithmeticFunction.moebius d : ℝ) else 0 := by
      apply sum_congr rfl
      intro p _
      exact coprime_indicator_moebius p q hq
    _ = ∑ d ∈ q.divisors, ∑ p ∈ Icc ⌈l * q⌉ ⌊u * q⌋,
        if (d : ℤ) ∣ p then (ArithmeticFunction.moebius d : ℝ) else 0 :=
      sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro d hd
      rw [← sum_filter, sum_const, nsmul_eq_mul,
        multiples_interval_card _ _ d (Nat.pos_of_mem_divisors hd)]
      ring

/-- The divisor identity for Euler's totient, with real division. -/
theorem totient_eq_moebius_sum (q : ℕ) (hq : 0 < q) :
    (Nat.totient q : ℝ) = ∑ d ∈ q.divisors,
      (ArithmeticFunction.moebius d : ℝ) * ((q : ℝ) / d) := by
  have hsum : ∀ (n : ℕ), n > 0 → ∑ d ∈ n.divisors, (Nat.totient d : ℝ) = (n : ℝ) := by
    intro n _
    exact_mod_cast Nat.sum_totient n
  have h := ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp hsum q hq
  rw [Nat.sum_divisorsAntidiagonal (fun d e => (ArithmeticFunction.moebius d : ℝ) * (e : ℝ))] at h
  rw [← h]
  apply sum_congr rfl
  intro d hd
  rw [Nat.cast_div (Nat.dvd_of_mem_divisors hd)
    (by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne' : (d : ℝ) ≠ 0)]

/-- Explicit uniform version of N_q(J) = |J| phi(q) + O(tau_0(q)).
The implied constant here is exactly one, for every positive q. -/
theorem reducedNumerators_card_discrepancy (l u : ℝ) (hlu : l ≤ u)
    (q : ℕ) (hq : 0 < q) :
    |((reducedNumerators l u q).card : ℝ) - (u - l) * Nat.totient q| ≤
      (q.divisors.card : ℝ) := by
  rw [reducedNumerators_card_moebius l u q hq, totient_eq_moebius_sum q hq,
    mul_sum, ← sum_sub_distrib]
  calc
    |∑ d ∈ q.divisors, ((ArithmeticFunction.moebius d : ℝ) *
        ((Icc ⌈l * q / d⌉ ⌊u * q / d⌋).card : ℝ) -
        (u - l) * ((ArithmeticFunction.moebius d : ℝ) * ((q : ℝ) / d)))| ≤
        ∑ d ∈ q.divisors, |(ArithmeticFunction.moebius d : ℝ)| * 1 := by
      apply le_trans (abs_sum_le_sum_abs _ _)
      apply sum_le_sum
      intro d hd
      have hdR : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
      have hi := integer_interval_card_discrepancy (l * q / d) (u * q / d)
        (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hlu (Nat.cast_nonneg q)) hdR.le)
      have hid : u * (q : ℝ) / d - l * q / d = (u - l) * ((q : ℝ) / d) := by ring
      rw [hid] at hi
      rw [show (ArithmeticFunction.moebius d : ℝ) *
          ((Icc ⌈l * q / d⌉ ⌊u * q / d⌋).card : ℝ) -
          (u - l) * ((ArithmeticFunction.moebius d : ℝ) * ((q : ℝ) / d)) =
          (ArithmeticFunction.moebius d : ℝ) *
          (((Icc ⌈l * q / d⌉ ⌊u * q / d⌋).card : ℝ) -
            (u - l) * ((q : ℝ) / d)) by ring, abs_mul]
      exact mul_le_mul_of_nonneg_left hi (abs_nonneg _)
    _ ≤ ∑ _d ∈ q.divisors, (1 : ℝ) := by
      apply sum_le_sum
      intro d _
      simp only [mul_one]
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
    _ = _ := by simp

/-- The reduced denominator fibers give an exact, nonredundant block count. -/
theorem sourceFractions_card_eq_sum_numerators (l u : ℝ) (Q : ℕ) (hQ : 0 < Q) :
    (sourceFractions l u Q).card =
      ∑ q ∈ Ico Q (2 * Q), (reducedNumerators l u q).card := by
  classical
  have hmap : Set.MapsTo Rat.den (sourceFractions l u Q : Set ℚ)
      (Ico Q (2 * Q) : Set ℕ) := by
    intro r hr
    exact mem_Ico.mpr ((mem_sourceFractions l u Q r).mp hr).2.2
  rw [card_eq_sum_card_fiberwise hmap]
  apply sum_congr rfl
  intro q hq
  have hqblock := mem_Ico.mp hq
  have hqpos : 0 < q := lt_of_lt_of_le hQ hqblock.1
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hqZ : (0 : ℤ) < q := by exact_mod_cast hqpos
  apply card_bij (fun r _ => r.num)
  · intro r hr
    obtain ⟨hr, hden⟩ := mem_filter.mp hr
    have h := (mem_sourceFractions l u Q r).mp hr
    apply (mem_reducedNumerators l u q r.num).mpr
    have hl : l ≤ (r.num : ℝ) / q := by
      simpa only [Rat.cast_def, hden] using h.1
    have hu : (r.num : ℝ) / q ≤ u := by
      simpa only [Rat.cast_def, hden] using h.2.1
    exact ⟨(le_div_iff₀ hqR).mp hl, (div_le_iff₀ hqR).mp hu,
      hden ▸ r.reduced⟩
  · intro r hr s hs hnum
    exact Rat.ext hnum ((mem_filter.mp hr).2.trans (mem_filter.mp hs).2.symm)
  · intro p hp
    have h := (mem_reducedNumerators l u q p).mp hp
    have hc : p.natAbs.Coprime (q : ℤ).natAbs := by simpa using h.2.2
    have hd : ((p : ℚ) / (q : ℚ)).den = q := by
      exact_mod_cast Rat.den_div_eq_of_coprime hqZ hc
    have hn : ((p : ℚ) / (q : ℚ)).num = p := by
      exact_mod_cast Rat.num_div_eq_of_coprime hqZ hc
    refine ⟨(p : ℚ) / (q : ℚ), mem_filter.mpr ⟨?_, hd⟩, hn⟩
    apply (mem_sourceFractions l u Q _).mpr
    simp only [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast, hd]
    exact ⟨(le_div_iff₀ hqR).mpr h.1, (div_le_iff₀ hqR).mpr h.2.1, hqblock⟩

/-- A finite, unconditional discrepancy estimate for the exact source set.
No asymptotic estimate for totients or divisor counts is assumed here. -/
theorem sourceFractions_totient_discrepancy (l u : ℝ) (hlu : l ≤ u)
    (Q : ℕ) (hQ : 0 < Q) :
    |((sourceFractions l u Q).card : ℝ) -
      (u - l) * ∑ q ∈ Ico Q (2 * Q), (Nat.totient q : ℝ)| ≤
      ∑ q ∈ Ico Q (2 * Q), (q.divisors.card : ℝ) := by
  rw [sourceFractions_card_eq_sum_numerators l u Q hQ, Nat.cast_sum,
    mul_sum, ← sum_sub_distrib]
  apply le_trans (abs_sum_le_sum_abs _ _)
  apply sum_le_sum
  intro q hq
  exact reducedNumerators_card_discrepancy l u hlu q
    (lt_of_lt_of_le hQ (mem_Ico.mp hq).1)

/-- Explicit lower bound before estimating the two arithmetic sums. -/
theorem sourceFractions_card_ge_totient_sub_divisors (l u : ℝ) (hlu : l ≤ u)
    (Q : ℕ) (hQ : 0 < Q) :
    (u - l) * (∑ q ∈ Ico Q (2 * Q), (Nat.totient q : ℝ)) -
      (∑ q ∈ Ico Q (2 * Q), (q.divisors.card : ℝ)) ≤
      ((sourceFractions l u Q).card : ℝ) := by
  have h := (abs_le.mp (sourceFractions_totient_discrepancy l u hlu Q hQ)).1
  linarith

end
end MahlerLean
