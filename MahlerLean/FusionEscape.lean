import MahlerLean.FusionRecursion

/-!
The infinite construction now supplies FusionData rather than assuming it.
The final escape theorem is conditional on FusionInputs, whose supply,
counting and finite-zero-set hypotheses still require analytic proofs.
We also verify uniqueness of the common point and unbounded source
denominators for the constructed sequence.
-/

namespace MahlerLean

open Set

/-- Two common points of fusion intervals must coincide. The source
errors are bounded by 2^(-(n+3)), so their mutual distance tends to zero. -/
theorem fusion_intersection_subsingleton {f : ℝ → ℝ} (d : FusionData f) :
    Set.Subsingleton {x : ℝ | ∀ n, x ∈ Icc (d.left n) (d.right n)} := by
  intro x hx y hy
  have herror (n : ℕ) (z : ℝ) (hz : ∀ k, z ∈ Icc (d.left k) (d.right k)) :
      |z - (d.center n : ℝ)| < ((2 : ℝ) ^ (n + 3))⁻¹ := by
    have hden : (2 : ℝ) ≤ (d.center n).den := by exact_mod_cast d.center_den n
    have hp : (2 : ℝ) ^ (n + 3) ≤ ((d.center n).den : ℝ) ^ (n + 3) :=
      pow_le_pow_left₀ (by norm_num) hden (n + 3)
    have hinv : (((d.center n).den : ℝ) ^ (n + 3))⁻¹ ≤
        ((2 : ℝ) ^ (n + 3))⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le (by positivity) hp
    exact lt_of_lt_of_le (d.source_approx n z (hz (n + 1))).2 hinv
  have hdist (n : ℕ) : |x - y| ≤ 2 * ((2 : ℝ) ^ (n + 3))⁻¹ := by
    have hxsmall := herror n x hx
    have hysmall := herror n y hy
    have htri := abs_sub_le x (d.center n : ℝ) y
    rw [abs_sub_comm (d.center n : ℝ) y] at htri
    linarith
  have hgeom : Filter.Tendsto (fun n : ℕ => ((2 : ℝ)⁻¹) ^ n)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hlim : Filter.Tendsto (fun n : ℕ => 2 * ((2 : ℝ) ^ (n + 3))⁻¹)
      Filter.atTop (nhds 0) := by
    have heq : (fun n : ℕ => 2 * ((2 : ℝ) ^ (n + 3))⁻¹) =
        (fun n : ℕ => (1 / 4 : ℝ) * ((2 : ℝ)⁻¹) ^ n) := by
      funext n
      simp only [pow_add, mul_inv_rev, ← inv_pow]
      norm_num
      ring
    rw [heq]
    simpa only [mul_zero] using hgeom.const_mul (1 / 4 : ℝ)
  have hzero : |x - y| ≤ 0 := ge_of_tendsto' hlim hdist
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hzero (abs_nonneg _)))

/-- FusionData has exactly one common point, using the existence theorem
from step 3 and the quantitative source-error bound above. -/
theorem exists_unique_fusion_point {f : ℝ → ℝ} (d : FusionData f) :
    ∃! x : ℝ, ∀ n, x ∈ Icc (d.left n) (d.right n) := by
  obtain ⟨x, hx, _hL, _hP, _havoid, _hnot⟩ := exists_escape_of_fusion_data f d
  exact ⟨x, hx, fun y hy => fusion_intersection_subsingleton d hy hx⟩

/-- The reduced source denominators of any recorded construction tend
to infinity, by their strict factor-two growth. -/
theorem fusion_denominators_tendsto {f : ℝ → ℝ} {d : FusionInputs f}
    (c : FusionConstruction d) :
    Filter.Tendsto (fun n => (c.center n).den) Filter.atTop Filter.atTop := by
  have hmono : StrictMono (fun n => (c.center n).den) :=
    strictMono_nat_of_lt_succ (fun n => by have := c.denominator_growth n; omega)
  exact hmono.tendsto_atTop

/-- The counting-to-escape implication, including initialization and the
infinite construction. Its conclusion is the explicit approximation bound
with exponent 100, not a statement about a separately defined supremum mu. -/
theorem exists_escape_of_counting {f : ℝ → ℝ} (d : FusionInputs f) :
    ∃ x : ℝ, ∃ B : ℕ, x ∈ Ioo d.left d.right ∧ 2 ≤ B ∧
      Liouville x ∧ PaperLiouville x ∧
      EventualTargetAvoidance (f x) 100 B ∧ ¬ Liouville (f x) := by
  let c := fusionConstruction d
  obtain ⟨x, hx, hL, hP, havoid, hnot⟩ := exists_escape_of_fusion_data f c.toFusionData
  exact ⟨x, c.cutoff 0, c.contained 0 (hx 0), c.cutoff_start, hL, hP, havoid, hnot⟩

end MahlerLean
