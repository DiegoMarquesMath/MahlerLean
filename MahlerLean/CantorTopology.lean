import MahlerLean.CantorSubtree
import Mathlib.Topology.Perfect
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecificLimits.Basic

/-!
Topological completion of the binary fusion construction.

The arithmetic part of the Cantor refinement is already contained in
CantorBranches.  This module proves the shrinking-node and endpoint facts
needed for perfectness and total disconnectedness.
-/

noncomputable section
namespace MahlerLean

open Set Filter
open scoped Topology

/-- A level-(n+1) interval has width bounded by a geometric quantity
depending only on n. -/
theorem cantorStage_width_lt_two_pow {f : ℝ → ℝ} (d : FusionInputs f)
    (n : ℕ) (omega : CantorPath (n + 1)) :
    (cantorStage d (n + 1) omega).right -
        (cantorStage d (n + 1) omega).left <
      2 * (((2 : ℝ) ^ n)⁻¹) := by
  let t := cantorTransition d n (Fin.tail omega)
  have hleft :=
    cantorStage_source d n omega
      (cantorStage d (n + 1) omega).left
      (left_mem_Icc.mpr (cantorStage d (n + 1) omega).nondegenerate.le)
  have hright :=
    cantorStage_source d n omega
      (cantorStage d (n + 1) omega).right
      (right_mem_Icc.mpr (cantorStage d (n + 1) omega).nondegenerate.le)
  dsimp only at hleft hright
  have hq2 : 2 ≤ (cantorTransition d n (Fin.tail omega)).center.den :=
    le_trans
      (cantorTransition d n (Fin.tail omega)).height_ge_two
      (cantorTransition d n (Fin.tail omega)).den_lower
  have hq2r :
      (2 : ℝ) ≤ ((cantorTransition d n (Fin.tail omega)).center.den : ℝ) := by
    exact_mod_cast hq2
  have h2n_pos : 0 < (2 : ℝ) ^ n := by positivity
  have hq_pos :
      0 < ((cantorTransition d n (Fin.tail omega)).center.den : ℝ) := by
    positivity
  have hpow_base :
      (2 : ℝ) ^ (n + 3) ≤
        ((cantorTransition d n (Fin.tail omega)).center.den : ℝ) ^ (n + 3) := by
    gcongr
  have hpow_exp : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ (n + 3) := by
    rw [pow_add]
    nlinarith [h2n_pos]
  have hpow :
      (2 : ℝ) ^ n ≤
        ((cantorTransition d n (Fin.tail omega)).center.den : ℝ) ^ (n + 3) :=
    hpow_exp.trans hpow_base
  have hinv :
      (((cantorTransition d n (Fin.tail omega)).center.den : ℝ) ^ (n + 3))⁻¹ ≤
        ((2 : ℝ) ^ n)⁻¹ := by
    rw [inv_le_inv₀ (pow_pos hq_pos _) h2n_pos]
    exact hpow
  have hl := (abs_lt.mp hleft.2)
  have hr := (abs_lt.mp hright.2)
  have hwidth :
      (cantorStage d (n + 1) omega).right -
          (cantorStage d (n + 1) omega).left <
        2 * (((cantorTransition d n (Fin.tail omega)).center.den : ℝ) ^
          (n + 3))⁻¹ := by
    linarith
  exact hwidth.trans_le (by gcongr)

/-- No left endpoint of a node belongs to the full limit set. -/
theorem cantorStage_left_not_mem_limitSet {f : ℝ → ℝ} (d : FusionInputs f)
    (n : ℕ) (omega : CantorPath n) :
    (cantorStage d n omega).left ∉ cantorLimitSet d := by
  intro hx
  have hxnode :
      (cantorStage d n omega).left ∈
        Icc (cantorStage d n omega).left (cantorStage d n omega).right :=
    left_mem_Icc.mpr (cantorStage d n omega).nondegenerate.le
  have hpath :
      cantorPathAt d (cantorStage d n omega).left hx n = omega :=
    cantorStage_path_unique d n
      (cantorPathAt_mem d (cantorStage d n omega).left hx n) hxnode
  have hchild :=
    cantorStage_nested d n
      (cantorPathAt d (cantorStage d n omega).left hx (n + 1))
      (cantorPathAt_mem d (cantorStage d n omega).left hx (n + 1))
  rw [cantorPathAt_tail d (cantorStage d n omega).left hx n, hpath] at hchild
  exact (lt_irrefl _ hchild.1)

/-- No right endpoint of a node belongs to the full limit set. -/
theorem cantorStage_right_not_mem_limitSet {f : ℝ → ℝ} (d : FusionInputs f)
    (n : ℕ) (omega : CantorPath n) :
    (cantorStage d n omega).right ∉ cantorLimitSet d := by
  intro hx
  have hxnode :
      (cantorStage d n omega).right ∈
        Icc (cantorStage d n omega).left (cantorStage d n omega).right :=
    right_mem_Icc.mpr (cantorStage d n omega).nondegenerate.le
  have hpath :
      cantorPathAt d (cantorStage d n omega).right hx n = omega :=
    cantorStage_path_unique d n
      (cantorPathAt_mem d (cantorStage d n omega).right hx n) hxnode
  have hchild :=
    cantorStage_nested d n
      (cantorPathAt d (cantorStage d n omega).right hx (n + 1))
      (cantorPathAt_mem d (cantorStage d n omega).right hx (n + 1))
  rw [cantorPathAt_tail d (cantorStage d n omega).right hx n, hpath] at hchild
  exact (lt_irrefl _ hchild.2)

end MahlerLean
