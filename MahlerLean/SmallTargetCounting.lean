import MahlerLean.SmallTargetBlockCounting
import MahlerLean.SmallTargetDyadicSums

open Set
noncomputable section
namespace MahlerLean

/-- Full small-target estimate with the original safety margin.
Constants are fixed before A,Q,H and before the source family. Blocks
crossing Q^(1/5) are included whenever their left endpoint is below it. -/
theorem exists_smallTarget_original_margin_card_bound
    {f : ℝ → ℝ} {a b F M m : ℝ}
    (hF : 0 ≤ F) (hM : 0 ≤ M) (hm : 0 < m)
    (hf : ∀ x ∈ Icc a b, |f x| ≤ F)
    (hinv : ∀ x ∈ Icc a b, ∀ z ∈ Icc a b, m*|x-z| ≤ |f x-f z|) :
    ∃ C_low C_err : ℝ, 0 < C_low ∧ 0 < C_err ∧
      ∀ A Q : ℕ, 3 ≤ A → 0 < Q → ∀ H : ℝ, 1 ≤ H → ∀ S : Finset ℚ,
        (∀ r ∈ S, r.den < 2*Q) →
        (∀ r ∈ S, (r : ℝ) ∈ Icc a b) →
        (∀ r ∈ S, ∃ k : ℕ, (2 : ℝ)^k*H < (Q : ℝ)^((1 : ℝ)/5) ∧
          ∃ p : ℤ, ∃ q : ℕ, 0 < q ∧ (2 : ℝ)^k*H ≤ (q : ℝ) ∧
            (q : ℝ) < 2*((2 : ℝ)^k*H) ∧
            |f r-(p : ℝ)/q| ≤ safetyMargin M Q A q) →
        (S.card : ℝ) ≤ C_low*(Q : ℝ)^2*(H^98)⁻¹ + C_err*(Q : ℝ)^((2 : ℝ)/5) := by
  classical
  let K : ℝ := 3*(4*(F+2+4*M)+3)
  let C₀ : ℝ := 16*K/m
  let C₁ : ℝ := K*(32*M/m+1)
  have hK : 0 < K := by dsimp [K]; positivity
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  have hC₁ : 0 < C₁ := by dsimp [C₁]; positivity
  refine ⟨2*C₀, 2*C₁, by positivity, by positivity, ?_⟩
  intro A Q hA hQ H hH S hden hx hw
  have hHpos : 0 < H := by linarith
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast hQ
  choose k hk using (fun r : ↑S ↦ hw r r.property)
  let t : Finset ℕ := Finset.univ.image k
  let B (j : ℕ) : ℝ := (2 : ℝ)^j*H
  let E (j : ℕ) : Finset ℚ := S.filter (fun r : ℚ ↦ ∃ p : ℤ, ∃ q : ℕ,
    0 < q ∧ B j ≤ (q : ℝ) ∧ (q : ℝ) < 2*B j ∧ |f r-(p : ℝ)/q| ≤ safetyMargin M Q A q)
  have hsmall : ∀ j ∈ t, B j < (Q : ℝ)^((1 : ℝ)/5) := by
    intro j hj
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hj
    exact (hk r).1
  have hcover : ∀ r ∈ S, ∃ j ∈ t, r ∈ E j := by
    intro r hr
    exact ⟨k ⟨r,hr⟩, Finset.mem_image.mpr ⟨⟨r,hr⟩, Finset.mem_univ _, rfl⟩,
      Finset.mem_filter.mpr ⟨hr, (hk ⟨r,hr⟩).2⟩⟩
  have hbound : ∀ j ∈ t, ((E j).card : ℝ) ≤ C₀*(Q : ℝ)^2*((B j)^98)⁻¹+C₁*(B j)^2 := by
    intro j _
    have hBj : 1 ≤ B j := by
      have hh := one_le_pow₀ (show (1 : ℝ) ≤ 2 by norm_num) (n := j)
      dsimp [B]
      nlinarith
    exact small_target_block_card_le (E j) hF hM hm hBj hQ (by omega) hf hinv
      (fun r hr ↦ hx r (Finset.mem_filter.mp hr).1)
      (fun r hr ↦ hden r (Finset.mem_filter.mp hr).1)
      (fun r hr ↦ (Finset.mem_filter.mp hr).2)
  have hc := card_le_sum_of_finite_cover S t E
    (fun j ↦ C₀*(Q : ℝ)^2*((B j)^98)⁻¹+C₁*(B j)^2) hcover hbound
  have hi := dyadic_inverse_power_sum_le t hHpos
  have hs := dyadic_square_sum_le t hHpos.le hsmall
  have he : ((Q : ℝ)^((1 : ℝ)/5))^2 = (Q : ℝ)^((2 : ℝ)/5) := by
    rw [← Real.rpow_mul_natCast hQpos.le]
    congr 1
    norm_num
  rw [he] at hs
  calc
    (S.card : ℝ) ≤ ∑ j ∈ t, (C₀*(Q : ℝ)^2*((B j)^98)⁻¹+C₁*(B j)^2) := hc
    _ = C₀*(Q : ℝ)^2*(∑ j ∈ t, ((B j)^98)⁻¹)+C₁*(∑ j ∈ t, (B j)^2) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ C₀*(Q : ℝ)^2*(2*(H^98)⁻¹)+C₁*(2*(Q : ℝ)^((2 : ℝ)/5)) :=
      add_le_add (mul_le_mul_of_nonneg_left hi (by positivity))
        (mul_le_mul_of_nonneg_left hs hC₁.le)
    _ = _ := by ring

end MahlerLean
