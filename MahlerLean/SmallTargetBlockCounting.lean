import MahlerLean.SmallTargetMargin

open Set
noncomputable section
namespace MahlerLean

theorem small_target_block_card_le_raw
    (S : Finset ℚ) {f : ℝ → ℝ} {a b F M m B : ℝ} {Q A : ℕ}
    (hF : 0 ≤ F) (hM : 0 ≤ M) (hm : 0 < m) (hB : 1 ≤ B) (hQ : 0 < Q)
    (hf : ∀ x ∈ Icc a b, |f x| ≤ F)
    (hinv : ∀ x ∈ Icc a b, ∀ z ∈ Icc a b, m*|x-z| ≤ |f x-f z|)
    (hx : ∀ r ∈ S, (r : ℝ) ∈ Icc a b)
    (hden : ∀ r ∈ S, r.den < 2*Q)
    (hw : ∀ r ∈ S, ∃ p : ℤ, ∃ q : ℕ, 0 < q ∧ B ≤ (q : ℝ) ∧ (q : ℝ) < 2*B ∧
      |f r-(p : ℝ)/q| ≤ safetyMargin M Q A q) :
    (S.card : ℝ) ≤ (3*(4*(F+2+4*M)+3)*B^2) *
      (4*(Q : ℝ)^2 * (2*(2*(B^100)⁻¹+4*M*((Q : ℝ)^A)⁻¹)/m)+1) := by
  classical
  let C := F+2+4*M
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let eps := 2*(B^100)⁻¹+4*M*((Q : ℝ)^A)⁻¹
  have heps : 0 ≤ eps := by dsimp [eps]; positivity
  let t := targetWitnessBox B C
  let E (w : ℕ × ℤ) := S.filter (fun r : ℚ ↦ |f r-(w.2 : ℝ)/w.1| ≤ eps)
  have he (w : ℕ × ℤ) : ((E w).card : ℝ) ≤ 4*(Q : ℝ)^2*(2*eps/m)+1 := by
    apply rational_target_neighborhood_card_le (E w) hm heps hQ hinv
    · intro r hr; exact hx r (Finset.mem_filter.mp hr).1
    · intro r hr; exact (Finset.mem_filter.mp hr).2
    · intro r hr; exact hden r (Finset.mem_filter.mp hr).1
  have hcov : ∀ r ∈ S, ∃ w ∈ t, r ∈ E w := by
    intro r hr
    obtain ⟨p,q,hq,hqlo,hqhi,herr⟩ := hw r hr
    have hp := target_witness_numerator_bound hM hQ hq (hf r (hx r hr)) herr
    refine ⟨(q,p), mem_targetWitnessBox hC hqhi hp, Finset.mem_filter.mpr ⟨hr, ?_⟩⟩
    exact herr.trans (safetyMargin_le_block (by linarith : 0 < B) hqlo)
  exact card_le_of_uniform_cell_bound S t E (by positivity)
    (targetWitnessBox_card_le hB hC) hcov (fun w _ ↦ he w)

/-- One small block: main H-sensitive term and a quadratic block error.
All constants depend only on the fixed interval data, not A,Q,B,H. -/
theorem small_target_block_card_le
    (S : Finset ℚ) {f : ℝ → ℝ} {a b F M m B : ℝ} {Q A : ℕ}
    (hF : 0 ≤ F) (hM : 0 ≤ M) (hm : 0 < m) (hB : 1 ≤ B) (hQ : 0 < Q) (hA : 2 ≤ A)
    (hf : ∀ x ∈ Icc a b, |f x| ≤ F)
    (hinv : ∀ x ∈ Icc a b, ∀ z ∈ Icc a b, m*|x-z| ≤ |f x-f z|)
    (hx : ∀ r ∈ S, (r : ℝ) ∈ Icc a b)
    (hden : ∀ r ∈ S, r.den < 2*Q)
    (hw : ∀ r ∈ S, ∃ p : ℤ, ∃ q : ℕ, 0 < q ∧ B ≤ (q : ℝ) ∧ (q : ℝ) < 2*B ∧
      |f r-(p : ℝ)/q| ≤ safetyMargin M Q A q) :
    (S.card : ℝ) ≤ (16*(3*(4*(F+2+4*M)+3))/m)*(Q : ℝ)^2*(B^98)⁻¹ +
      ((3*(4*(F+2+4*M)+3))*(32*M/m+1))*B^2 := by
  have hc := small_target_block_card_le_raw S hF hM hm hB hQ hf hinv hx hden hw
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hBp : 0 < B := by linarith
  have hid : B^2*(B^100)⁻¹ = (B^98)⁻¹ := by
    have he : B^100 = B^98*B^2 := by ring
    rw [he, mul_inv_rev]
    field_simp
  have hQA : (Q : ℝ)^2*((Q : ℝ)^A)⁻¹ ≤ 1 := by
    have hh := pow_le_pow_right₀ hQ1 hA
    exact (mul_inv_le_iff₀ (pow_pos hQ0 A)).mpr (by simpa using hh)
  let K := 3*(4*(F+2+4*M)+3)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have heq : (K*B^2)*(4*(Q : ℝ)^2*(2*(2*(B^100)⁻¹+4*M*((Q : ℝ)^A)⁻¹)/m)+1) =
      (16*K/m)*(Q : ℝ)^2*(B^98)⁻¹ + (K*(32*M/m*((Q : ℝ)^2*((Q : ℝ)^A)⁻¹)+1))*B^2 := by
    rw [← hid]
    ring
  change (S.card : ℝ) ≤ (16*K/m)*(Q : ℝ)^2*(B^98)⁻¹ + (K*(32*M/m+1))*B^2
  change (S.card : ℝ) ≤ (K*B^2)*_ at hc
  rw [heq] at hc
  refine hc.trans ?_
  gcongr
  simpa using mul_le_mul_of_nonneg_left hQA (show 0 ≤ 32*M/m by positivity)

end MahlerLean
