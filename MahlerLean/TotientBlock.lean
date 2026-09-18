import MahlerLean.FareyNumerators
import Mathlib.Algebra.BigOperators.Intervals

/-!
Elementary lower bounds for totient sums. A noncoprime pair has a common
prime divisor, hence a common divisor at least two different from four.
The reciprocal-square sum of those possible divisors is at most 11/18.
-/
namespace MahlerLean
noncomputable section
open Finset

/-- A finite reciprocal-square bound sufficient for a positive density
of coprime pairs; excluding the composite integer four improves the constant. -/
theorem reciprocal_squares_except_four_le (N : ℕ) :
    (∑ d ∈ (Icc 2 N).filter (fun d => d ≠ 4), (1 : ℝ) / (d : ℝ)^2) ≤ 11/18 := by
  have hlarge : ∀ (N : ℕ), N ≥ 4 →
      (∑ d ∈ Icc 2 N, if d = 4 then (0 : ℝ) else 1 / (d : ℝ)^2) ≤
        11/18 - 1 / (N : ℝ) := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => norm_num [sum_Icc_succ_top]
    | succ n hn ih =>
      rw [sum_Icc_succ_top (by omega)]
      have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hn4 : n + 1 ≠ 4 := by omega
      simp only [hn4, ↓reduceIte, Nat.cast_add, Nat.cast_one]
      have hstep : 1 / ((n : ℝ) + 1)^2 ≤ 1 / (n : ℝ) - 1 / ((n : ℝ) + 1) := by
        apply (div_le_iff₀ (sq_pos_of_pos (by positivity : (0 : ℝ) < n + 1))).mpr
        field_simp
        nlinarith
      linarith
  rw [sum_filter]
  simp only [ite_not]
  by_cases hN : 4 ≤ N
  · exact (hlarge N hN).trans (sub_le_self _ (by positivity))
  · interval_cases N <;> norm_num [sum_Icc_succ_top]

/-- Exact cardinality of the positive multiples of d up to N. -/
theorem positive_multiples_card (N d : ℕ) :
    ((Icc 1 N).filter (fun k => d ∣ k)).card = N / d := by
  rw [← Nat.card_multiples' N d]
  congr 1
  ext k
  simp only [mem_filter, mem_Icc, mem_range]
  omega

/-- In the positive square [1,N]^2, at most 11/18 of all pairs
are noncoprime. The estimate uses a union bound over common divisors. -/
theorem noncoprime_pairs_card_le (N : ℕ) :
    ((((Icc 1 N).product (Icc 1 N)).filter
      (fun x : ℕ × ℕ => ¬ x.1.Coprime x.2)).card : ℝ) ≤
      (11/18 : ℝ) * (N : ℝ)^2 := by
  classical
  let D := (Icc 2 N).filter (fun d => d ≠ 4)
  let M (d : ℕ) := (Icc 1 N).filter (fun k => d ∣ k)
  have hcover : ((Icc 1 N).product (Icc 1 N)).filter
      (fun x : ℕ × ℕ => ¬ x.1.Coprime x.2) ⊆
        D.biUnion (fun d => (M d).product (M d)) := by
    intro x hx
    obtain ⟨hx, hbad⟩ := mem_filter.mp hx
    obtain ⟨hx1, hx2⟩ := mem_product.mp hx
    obtain ⟨d, hdprime, hd⟩ := Nat.exists_prime_and_dvd hbad
    have hd1 : d ∣ x.1 := dvd_trans hd (Nat.gcd_dvd_left _ _)
    have hd2 : d ∣ x.2 := dvd_trans hd (Nat.gcd_dvd_right _ _)
    have hdle : d ≤ N := (Nat.le_of_dvd (mem_Icc.mp hx1).1 hd1).trans (mem_Icc.mp hx1).2
    have hd4 : d ≠ 4 := by rintro rfl; exact (by decide : ¬ Nat.Prime 4) hdprime
    apply mem_biUnion.mpr
    exact ⟨d, mem_filter.mpr ⟨mem_Icc.mpr ⟨hdprime.two_le, hdle⟩, hd4⟩,
      mem_product.mpr ⟨mem_filter.mpr ⟨hx1, hd1⟩, mem_filter.mpr ⟨hx2, hd2⟩⟩⟩
  calc
    _ ≤ ((D.biUnion (fun d => (M d).product (M d))).card : ℝ) := by
      exact_mod_cast card_le_card hcover
    _ ≤ ∑ d ∈ D, (((M d).product (M d)).card : ℝ) := by
      exact_mod_cast (card_biUnion_le (s := D) (t := fun d => (M d).product (M d)))
    _ = ∑ d ∈ D, ((N / d : ℕ) : ℝ)^2 := by
      apply sum_congr rfl
      intro d _
      simp [M, card_product, positive_multiples_card, pow_two]
    _ ≤ ∑ d ∈ D, (N : ℝ)^2 * (1 / (d : ℝ)^2) := by
      apply sum_le_sum
      intro d _
      have h : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d := Nat.cast_div_le
      have hh := mul_self_le_mul_self (by positivity) h
      convert hh using 1 <;> ring
    _ = (N : ℝ)^2 * ∑ d ∈ D, (1 : ℝ) / (d : ℝ)^2 := (mul_sum _ _ _).symm
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (reciprocal_squares_except_four_le N)
        (sq_nonneg (N : ℝ))
      simpa only [D, mul_comm] using h

/-- Count coprime pairs on or below the positive diagonal by their
second coordinate. The q=1 term is represented by (1,1). -/
theorem coprime_triangle_card (N : ℕ) :
    (((Icc 1 N).product (Icc 1 N)).filter
      (fun x : ℕ × ℕ => x.1 ≤ x.2 ∧ x.1.Coprime x.2)).card =
      ∑ q ∈ Icc 1 N, Nat.totient q := by
  classical
  let T := ((Icc 1 N).product (Icc 1 N)).filter
    (fun x : ℕ × ℕ => x.1 ≤ x.2 ∧ x.1.Coprime x.2)
  have hmap : Set.MapsTo Prod.snd (T : Set (ℕ × ℕ)) (Icc 1 N : Set ℕ) := by
    intro x hx
    exact (mem_product.mp (mem_filter.mp hx).1).2
  change T.card = _
  rw [card_eq_sum_card_fiberwise hmap]
  apply sum_congr rfl
  intro q hq
  have ht : ((Icc 1 q).filter (fun p => q.Coprime p)).card = Nat.totient q := by
    simpa only [Nat.add_comm 1 q, Ico_add_one_right_eq_Icc] using
      Nat.filter_coprime_Ico_eq_totient q 1
  rw [← ht]
  apply card_bij (fun x _ => x.1)
  · intro x hx
    obtain ⟨hx, hqeq⟩ := mem_filter.mp hx
    obtain ⟨hxmem, hxle, hcop⟩ := mem_filter.mp hx
    apply mem_filter.mpr
    exact ⟨mem_Icc.mpr ⟨(mem_Icc.mp (mem_product.mp hxmem).1).1,
      hqeq ▸ hxle⟩, hqeq ▸ hcop.symm⟩
  · intro x hx y hy h
    exact Prod.ext h ((mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm)
  · intro p hp
    obtain ⟨hpmem, hcop⟩ := mem_filter.mp hp
    refine ⟨(p,q), mem_filter.mpr ⟨?_, rfl⟩, rfl⟩
    apply mem_filter.mpr
    refine ⟨mem_product.mpr ⟨?_, hq⟩, (mem_Icc.mp hpmem).2, hcop.symm⟩
    exact mem_Icc.mpr ⟨(mem_Icc.mp hpmem).1,
      (mem_Icc.mp hpmem).2.trans (mem_Icc.mp hq).2⟩

/-- Reflection in the diagonal bounds the coprime square by two triangles. -/
theorem coprime_pairs_card_le_twice_totient_sum (N : ℕ) :
    (((Icc 1 N).product (Icc 1 N)).filter
      (fun x : ℕ × ℕ => x.1.Coprime x.2)).card ≤
      2 * ∑ q ∈ Icc 1 N, Nat.totient q := by
  classical
  let T := ((Icc 1 N).product (Icc 1 N)).filter
    (fun x : ℕ × ℕ => x.1 ≤ x.2 ∧ x.1.Coprime x.2)
  have hcover : ((Icc 1 N).product (Icc 1 N)).filter
      (fun x : ℕ × ℕ => x.1.Coprime x.2) ⊆ T ∪ T.image Prod.swap := by
    intro x hx
    obtain ⟨hxmem, hcop⟩ := mem_filter.mp hx
    rcases le_total x.1 x.2 with h | h
    · exact mem_union_left _ (mem_filter.mpr ⟨hxmem, h, hcop⟩)
    · apply mem_union_right
      apply mem_image.mpr
      refine ⟨x.swap, ?_, Prod.swap_swap x⟩
      exact mem_filter.mpr ⟨mem_product.mpr
        ⟨(mem_product.mp hxmem).2, (mem_product.mp hxmem).1⟩, h, hcop.symm⟩
  calc
    _ ≤ (T ∪ T.image Prod.swap).card := card_le_card hcover
    _ ≤ T.card + (T.image Prod.swap).card := card_union_le _ _
    _ ≤ T.card + T.card := Nat.add_le_add_left card_image_le _
    _ = _ := by rw [show T.card = _ from coprime_triangle_card N]; omega

/-- Elementary summatory totient lower bound, without zeta asymptotics. -/
theorem totient_sum_lower (N : ℕ) :
    (7/36 : ℝ) * (N : ℝ)^2 ≤ ∑ q ∈ Icc 1 N, (Nat.totient q : ℝ) := by
  classical
  let P := (Icc 1 N).product (Icc 1 N)
  have hpartition : (P.filter (fun x => x.1.Coprime x.2)).card +
      (P.filter (fun x => ¬ x.1.Coprime x.2)).card = N^2 := by
    rw [filter_card_add_filter_neg_card_eq_card]
    simp [P, card_product, pow_two]
  have hpartR : ((P.filter (fun x => x.1.Coprime x.2)).card : ℝ) +
      ((P.filter (fun x => ¬ x.1.Coprime x.2)).card : ℝ) = (N : ℝ)^2 := by
    exact_mod_cast hpartition
  have hgood : ((P.filter (fun x => x.1.Coprime x.2)).card : ℝ) ≤
      2 * ∑ q ∈ Icc 1 N, (Nat.totient q : ℝ) := by
    exact_mod_cast coprime_pairs_card_le_twice_totient_sum N
  have hbad := noncoprime_pairs_card_le N
  change ((P.filter (fun x => ¬ x.1.Coprime x.2)).card : ℝ) ≤ _ at hbad
  linarith

/-- The elementary triangular upper bound for the summatory totient. -/
theorem totient_sum_upper (N : ℕ) :
    (∑ q ∈ Icc 1 N, (Nat.totient q : ℝ)) ≤ (N : ℝ) * (N + 1) / 2 := by
  have hid : (∑ q ∈ Icc 1 N, (q : ℝ)) = (N : ℝ) * (N + 1) / 2 := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [sum_Icc_succ_top (by omega), ih]
      push_cast
      ring
  rw [← hid]
  apply sum_le_sum
  intro q _
  exact_mod_cast Nat.totient_le q

/-- The zero totient contributes nothing when passing between the two sum conventions. -/
theorem totient_sum_range_succ (N : ℕ) :
    (∑ q ∈ range (N + 1), (Nat.totient q : ℝ)) =
      ∑ q ∈ Icc 1 N, (Nat.totient q : ℝ) := by
  have he : range (N + 1) = insert 0 (Icc 1 N) := by
    ext q
    simp only [mem_range, mem_insert, mem_Icc]
    omega
  rw [he, sum_insert (by simp)]
  simp

/-- A positive quadratic lower bound on each denominator block.
The leading constant 5/18 is strictly larger than the required 1/4. -/
theorem totient_block_lower (Q : ℕ) :
    (5/18 : ℝ) * (Q : ℝ)^2 - (5/2 : ℝ) * Q ≤
      ∑ q ∈ Ico Q (2 * Q), (Nat.totient q : ℝ) := by
  have hbig : (∑ q ∈ range (2 * Q), (Nat.totient q : ℝ)) +
      (Nat.totient (2 * Q) : ℝ) = ∑ q ∈ Icc 1 (2 * Q), (Nat.totient q : ℝ) := by
    rw [← sum_range_succ, totient_sum_range_succ]
  have hsmall : (∑ q ∈ range Q, (Nat.totient q : ℝ)) +
      (Nat.totient Q : ℝ) = ∑ q ∈ Icc 1 Q, (Nat.totient q : ℝ) := by
    rw [← sum_range_succ, totient_sum_range_succ]
  have hl := totient_sum_lower (2 * Q)
  have hu := totient_sum_upper Q
  have hphi : (Nat.totient (2 * Q) : ℝ) ≤ 2 * (Q : ℝ) := by
    exact_mod_cast Nat.totient_le (2 * Q)
  have hn : (0 : ℝ) ≤ Nat.totient Q := Nat.cast_nonneg _
  rw [sum_Ico_eq_sub _ (by omega)]
  push_cast at hl
  nlinarith

end
end MahlerLean
