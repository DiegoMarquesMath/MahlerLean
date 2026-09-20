import MahlerLean.LargeTargetBlockCounting
import MahlerLean.DyadicTargetBlocks

open Set Filter
noncomputable section
namespace MahlerLean

/-- Sum all large dyadic target blocks. The cells, the finite index set and
its logarithmic cardinality are constructed in the proof. The constants and
threshold are chosen before the lower target cutoff H. -/
theorem exists_largeTarget_dyadic_card_bound
    {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hf : AnalyticOnNhd ℝ f U) (A : ℕ)
    {a b K₀ : ℝ} (hab : a < b) (hI : Icc a b ⊆ U) (hK₀ : 0 ≤ K₀)
    (hW : ∀ d : ℕ, 2 ≤ d → d ≤ wronskianDegreeCutoff A →
      ∀ z ∈ Icc a b, rationalWronskian f d z ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∃ Q₀ : ℝ, 2 ≤ Q₀ ∧
      ∀ Q : ℕ, Q₀ ≤ (Q : ℝ) → ∀ H : ℝ, 1 ≤ H → ∀ S : Finset ℚ,
        (∀ r ∈ S, r.den < 2 * Q) →
        (∀ r ∈ S, (r : ℝ) ∈ Icc a b) →
        (∀ r ∈ S, ∃ k : ℕ,
          (Q : ℝ) ^ ((1 : ℝ)/5) ≤ (2 : ℝ)^k * H ∧
          (2 : ℝ)^k * H < (Q : ℝ) ^ ((A : ℝ)/97) ∧
          ∃ y : ℚ, (y.den : ℝ) ≤ 2 * ((2 : ℝ)^k * H) ∧
            |(y : ℝ) - f r| ≤ K₀ * (Q : ℝ) ^
              (-largeTargetS A (Real.logb (Q : ℝ) ((2 : ℝ)^k * H)))) →
        (S.card : ℝ) ≤ C * (Q : ℝ) ^ ((17 : ℝ)/10) := by
  classical
  obtain ⟨C, hC, Qblock, _, hblock⟩ :=
    exists_uniform_largeTarget_block_card_bound hU hf A hab hI hK₀ hW
  obtain ⟨Qlog, hlog⟩ := eventually_atTop.mp eventually_log_mul_large_block_power_le
  let L : ℝ := (((A : ℝ)/97) + 1) / Real.log 2
  have hL : 0 < L := by
    dsimp [L]
    apply div_pos _ (Real.log_pos (by norm_num))
    positivity
  refine ⟨C * L, mul_pos hC hL, max 2 (max Qblock Qlog), le_max_left _ _, ?_⟩
  intro Q hQ H hH S hden hx hw
  have hQ2 : (2 : ℝ) ≤ Q := (le_max_left _ _).trans hQ
  have hQB : Qblock ≤ (Q : ℝ) := (le_max_left _ _).trans ((le_max_right _ _).trans hQ)
  have hQL : Qlog ≤ (Q : ℝ) := (le_max_right _ _).trans ((le_max_right _ _).trans hQ)
  have hQpos : (0 : ℝ) < Q := by linarith
  let B (k : ℕ) : ℝ := (2 : ℝ)^k * H
  let u (k : ℕ) : ℝ := Real.logb (Q : ℝ) (B k)
  let n := ⌈((A : ℝ)/97) * Real.log (Q : ℝ) / Real.log 2⌉₊
  let t := (Finset.range n).filter (fun k ↦
    (Q : ℝ)^((1 : ℝ)/5) ≤ B k ∧ B k < (Q : ℝ)^((A : ℝ)/97))
  let E (k : ℕ) : Finset ℚ := S.filter (fun r : ℚ ↦ ∃ y : ℚ,
    (y.den : ℝ) ≤ 2 * B k ∧ |(y : ℝ) - f r| ≤ K₀ * (Q : ℝ)^(-largeTargetS A (u k)))
  have hcover : ∀ r ∈ S, ∃ k ∈ t, r ∈ E k := by
    intro r hr
    obtain ⟨k, hklo, hkhi, y, hyden, hyerr⟩ := hw r hr
    have hkn : k < n := dyadic_index_lt_uniform_count hQ2 hH hkhi
    exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hkn, hklo, hkhi⟩,
      Finset.mem_filter.mpr ⟨hr, y, hyden, hyerr⟩⟩
  have hEc : ∀ k ∈ t, ((E k).card : ℝ) ≤ C * (Q : ℝ)^((33 : ℝ)/20) := by
    intro k hk
    obtain ⟨_, hklo, hkhi⟩ := Finset.mem_filter.mp hk
    obtain ⟨hBu, hu, huA⟩ := large_block_log_exponent hQ2 hklo hkhi
    apply hblock Q hQB (u k) hu (by dsimp [u]; linarith) (E k)
    · intro r hr; exact hden r (Finset.mem_filter.mp hr).1
    · intro r hr; exact hx r (Finset.mem_filter.mp hr).1
    · intro r hr
      obtain ⟨y, hyden, hyerr⟩ := (Finset.mem_filter.mp hr).2
      refine ⟨y, ?_, hyerr⟩
      simpa only [u, hBu] using hyden
  have ht : (t.card : ℝ) ≤ L * Real.log (Q : ℝ) := by
    have htn : t.card ≤ n := by
      exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range n)
    have htnR : (t.card : ℝ) ≤ (n : ℝ) := by exact_mod_cast htn
    exact htnR.trans (uniform_dyadic_count_le_log hQ2 (by positivity))
  have hb := card_le_of_uniform_cell_bound S t E
    (mul_nonneg hC.le (Real.rpow_nonneg hQpos.le _)) ht hcover hEc
  calc
    (S.card : ℝ) ≤ (L * Real.log (Q : ℝ)) * (C * (Q : ℝ)^((33 : ℝ)/20)) := hb
    _ = (C * L) * (Real.log (Q : ℝ) * (Q : ℝ)^((33 : ℝ)/20)) := by ring
    _ ≤ (C * L) * (Q : ℝ)^((17 : ℝ)/10) :=
      mul_le_mul_of_nonneg_left (hlog Q hQL) (mul_pos hC hL).le

end MahlerLean
