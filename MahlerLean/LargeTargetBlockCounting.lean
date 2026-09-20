import MahlerLean.UniformLargeTargetCounting
import MahlerLean.SourceCellCover

open Set
noncomputable section
namespace MahlerLean

theorem exists_uniform_largeTarget_block_card_bound
    {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hf : AnalyticOnNhd ℝ f U) (A : ℕ)
    {a b K₀ : ℝ} (hab : a < b) (hI : Icc a b ⊆ U)
    (hK₀ : 0 ≤ K₀)
    (hW : ∀ d : ℕ, 2 ≤ d → d ≤ wronskianDegreeCutoff A →
      ∀ z ∈ Icc a b, rationalWronskian f d z ≠ 0) :
    ∃ M : ℝ, 0 < M ∧
    ∃ Q₀ : ℝ, 1 ≤ Q₀ ∧ ∀ Q : ℕ, Q₀ ≤ (Q : ℝ) →
      ∀ u : ℝ, (1 : ℝ) / 5 ≤ u → 97 * u < (A : ℝ) →
      ∀ S : Finset ℚ,
        (∀ r ∈ S, r.den < 2 * Q) →
        (∀ r ∈ S, (r : ℝ) ∈ Icc a b) →
        (∀ r ∈ S, ∃ y : ℚ, (y.den : ℝ) ≤ 2 * (Q : ℝ) ^ u ∧
          |(y : ℝ) - f r| ≤ K₀ * (Q : ℝ) ^ (-largeTargetS A u)) →
        (S.card : ℝ) ≤ M * (Q : ℝ) ^ ((33 : ℝ) / 20) := by
  classical
  obtain ⟨M, hM, Q₀, hQ₀, hcell⟩ :=
    exists_uniform_largeTarget_interval_cell_card_bound hU hf A hab hI hK₀ hW
  refine ⟨(b-a+1)*M, mul_pos (by linarith) hM, Q₀, hQ₀, ?_⟩
  intro Q hQ u hu huA S hden hx hw
  have hQ1 : (1 : ℝ) ≤ Q := hQ₀.trans hQ
  have hQpos : (0 : ℝ) < Q := lt_of_lt_of_le zero_lt_one hQ1
  let ρ : ℝ := (Q : ℝ) ^ (-largeTargetKappa u)
  have hρ : 0 < ρ := Real.rpow_pos_of_pos hQpos _
  obtain ⟨n, _, hn, c, hc, hcover⟩ := exists_source_cell_cover hab hρ
  let E (i : Fin n) := S.filter (fun r : ℚ ↦ (r : ℝ) ∈ Icc (c i) b ∧ (r : ℝ) - c i ≤ ρ)
  have hEc (i : Fin n) : ((E i).card : ℝ) ≤ M := by
    apply hcell Q hQ u hu huA (c i) (hc i).1 (hc i).2 (E i)
    · intro r hr; exact hden r (Finset.mem_filter.mp hr).1
    · intro r hr; exact (Finset.mem_filter.mp hr).2.1
    · intro r hr; exact (Finset.mem_filter.mp hr).2.2
    · intro r hr; exact hw r (Finset.mem_filter.mp hr).1
  have hcov : ∀ r ∈ S, ∃ i ∈ (Finset.univ : Finset (Fin n)), r ∈ E i := by
    intro r hr
    obtain ⟨i, hi, hiρ⟩ := hcover r (hx r hr)
    exact ⟨i, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hr, hi, hiρ⟩⟩
  have hp := Real.rpow_le_rpow_of_exponent_le hQ1 (largeTargetKappa_le u)
  have hp1 : 1 ≤ (Q : ℝ) ^ ((33 : ℝ) / 20) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num : (0 : ℝ) ≤ 33/20)
  have hn' : (n : ℝ) ≤ (b-a+1) * (Q : ℝ) ^ ((33 : ℝ) / 20) := by
    dsimp [ρ] at hn
    rw [Real.rpow_neg hQpos.le, div_inv_eq_mul] at hn
    nlinarith [mul_le_mul_of_nonneg_left hp (sub_pos.mpr hab).le]
  have hb := card_le_of_uniform_cell_bound S Finset.univ E hM.le
    (by simpa using hn') hcov (fun i _ ↦ hEc i)
  convert hb using 1; ring

end MahlerLean
