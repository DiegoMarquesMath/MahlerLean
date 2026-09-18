import MahlerLean.TotientBlock
import MahlerLean.CountingToSafeCenter
import Mathlib.Data.Nat.Sqrt

namespace MahlerLean
noncomputable section
open Finset Filter Topology

/-- Divisors pair across the square root. -/
theorem divisors_card_le_twice_sqrt (n : ℕ) :
    n.divisors.card ≤ 2 * Nat.sqrt n := by
  classical
  by_cases hn : n = 0
  · simp [hn]
  let S := n.divisors.filter (fun d => d ≤ Nat.sqrt n)
  have hs : S.card ≤ Nat.sqrt n := by
    calc
      S.card ≤ (Icc 1 (Nat.sqrt n)).card := card_le_card (by
        intro d hd
        obtain ⟨hd, hsmall⟩ := mem_filter.mp hd
        exact mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd, hsmall⟩)
      _ = _ := by simp
  have hcover : n.divisors ⊆ S ∪ S.image (fun d => n / d) := by
    intro d hd
    by_cases hsmall : d ≤ Nat.sqrt n
    · exact mem_union_left _ (mem_filter.mpr ⟨hd, hsmall⟩)
    · have hdvd := Nat.dvd_of_mem_divisors hd
      have hprod := Nat.div_mul_cancel hdvd
      have hsmall' : n / d ≤ Nat.sqrt n := by
        have hnlt := Nat.lt_succ_sqrt n
        by_contra h
        have h1 : Nat.sqrt n + 1 ≤ d := by omega
        have h2 : Nat.sqrt n + 1 ≤ n / d := by omega
        have := Nat.mul_le_mul h2 h1
        nlinarith
      apply mem_union_right
      exact mem_image.mpr ⟨n / d,
        mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hdvd, hn⟩, hsmall'⟩,
        Nat.div_div_self hdvd hn⟩
  calc
    n.divisors.card ≤ (S ∪ S.image (fun d => n / d)).card := card_le_card hcover
    _ ≤ S.card + (S.image (fun d => n / d)).card := card_union_le _ _
    _ ≤ S.card + S.card := Nat.add_le_add_left (card_image_le) _
    _ ≤ 2 * Nat.sqrt n := by omega

/-- A coarse but subquadratic bound for the divisor error in a block. -/
theorem block_divisors_card_le (Q : ℕ) :
    (∑ q ∈ Ico Q (2 * Q), q.divisors.card) ≤ 2 * Q * Nat.sqrt (2 * Q) := by
  calc
    (∑ q ∈ Ico Q (2 * Q), q.divisors.card) ≤
        ∑ _q ∈ Ico Q (2 * Q), 2 * Nat.sqrt (2 * Q) := by
      apply sum_le_sum
      intro q hq
      exact (divisors_card_le_twice_sqrt q).trans
        (Nat.mul_le_mul_left 2 (Nat.sqrt_le_sqrt (mem_Ico.mp hq).2.le))
    _ = _ := by
      have hc : (Ico Q (2 * Q)).card = Q := by
        rw [Nat.card_Ico]
        omega
      rw [sum_const, nsmul_eq_mul, hc]
      norm_cast
      ring

/-- An explicit finite lower estimate, with a square-root divisor error. -/
theorem sourceFractions_card_lower_explicit (l u : ℝ) (hlu : l ≤ u)
    (Q : ℕ) (hQ : 0 < Q) :
    (u - l) * ((5/18 : ℝ) * (Q : ℝ)^2 - (5/2 : ℝ) * Q) -
      2 * (Q : ℝ) * Nat.sqrt (2 * Q) ≤ ((sourceFractions l u Q).card : ℝ) := by
  have h := sourceFractions_card_ge_totient_sub_divisors l u hlu Q hQ
  have ht := mul_le_mul_of_nonneg_left (totient_block_lower Q) (sub_nonneg.mpr hlu)
  have he : (∑ q ∈ Ico Q (2 * Q), (q.divisors.card : ℝ)) ≤
      2 * (Q : ℝ) * Nat.sqrt (2 * Q) := by
    exact_mod_cast block_divisors_card_le Q
  linarith

/-- Lemma 2.2, with the manuscript constant 1/4, proved from elementary
finite counting. The denominator threshold may depend on the interval. -/
theorem sourceFractions_quarter_supply (l u : ℝ) (hlu : l < u) :
    HasSourceSupply l u (1/4) := by
  let L := u - l
  have hL : 0 < L := sub_pos.mpr hlu
  obtain ⟨N, hN⟩ := exists_nat_gt (41472 / L^2)
  refine ⟨max 180 N, ?_⟩
  intro Q hQ
  have hQ180 : 180 ≤ Q := le_trans (le_max_left _ _) hQ
  have hNQ : N ≤ Q := le_trans (le_max_right _ _) hQ
  have hQR : (180 : ℝ) ≤ Q := by exact_mod_cast hQ180
  have hQpos : 0 < Q := by omega
  have hQposR : (0 : ℝ) < Q := by exact_mod_cast hQpos
  have hscale : 41472 ≤ L^2 * (Q : ℝ) := by
    have h : 41472 / L^2 ≤ (Q : ℝ) := hN.le.trans (by exact_mod_cast hNQ)
    have ht := (div_le_iff₀ (sq_pos_of_pos hL)).mp h
    nlinarith
  have hscaleQ := mul_le_mul_of_nonneg_right hscale hQposR.le
  have hs : (Nat.sqrt (2 * Q) : ℝ)^2 ≤ 2 * (Q : ℝ) := by
    exact_mod_cast Nat.sqrt_le' (2 * Q)
  have hroot : 144 * (Nat.sqrt (2 * Q) : ℝ) ≤ L * (Q : ℝ) := by
    have hsq : (144 * (Nat.sqrt (2 * Q) : ℝ))^2 ≤ (L * (Q : ℝ))^2 := by
      nlinarith
    exact (sq_le_sq₀ (by positivity) (by positivity)).mp hsq
  have herr := mul_le_mul_of_nonneg_right hroot hQposR.le
  have hlin := mul_nonneg (mul_pos hL hQposR).le (sub_nonneg.mpr hQR)
  have hlower := sourceFractions_card_lower_explicit l u hlu.le Q hQpos
  change L * ((5/18 : ℝ) * (Q : ℝ)^2 - (5/2 : ℝ) * Q) -
      2 * (Q : ℝ) * Nat.sqrt (2 * Q) ≤ _ at hlower
  change (1/4 : ℝ) * L * (Q : ℝ)^2 ≤ _
  nlinarith

/-- Positive-threshold form of Lemma 2.2 for every nondegenerate compact interval. -/
theorem exists_source_supply_threshold (l u : ℝ) (hlu : l < u) :
    ∃ Q₀ : ℕ, 0 < Q₀ ∧ ∀ Q ≥ Q₀,
      (1/4 : ℝ) * (u - l) * (Q : ℝ)^2 ≤ ((sourceFractions l u Q).card : ℝ) := by
  obtain ⟨Q₀, hQ₀⟩ := sourceFractions_quarter_supply l u hlu
  exact ⟨max 1 Q₀, lt_of_lt_of_le (by omega) (le_max_left _ _),
    fun Q hQ => hQ₀ Q (le_trans (le_max_right _ _) hQ)⟩

end
end MahlerLean
