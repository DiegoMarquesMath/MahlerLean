import MahlerLean.CantorTree
import MahlerLean.FusionConclusion
import MahlerLean.IrrationalityExponent

/-!
Coherent branches through the binary fusion tree.

A point of the limit set belongs to exactly one interval at each level.
This turns the levelwise compact construction into a genuine branch, whose
fusion invariants can be packaged in the existing FusionData structure.
-/

noncomputable section
namespace MahlerLean

open Set

/-- Distinct nodes at one level are strictly ordered and separated. -/
theorem cantorStage_order_separated_of_ne {f : ℝ → ℝ} (d : FusionInputs f) :
    ∀ n : ℕ, ∀ omega eta : CantorPath n, omega ≠ eta →
      (cantorStage d n omega).right < (cantorStage d n eta).left ∨
      (cantorStage d n eta).right < (cantorStage d n omega).left := by
  intro n
  induction n with
  | zero =>
      intro omega eta hne
      exact (hne (Subsingleton.elim omega eta)).elim
  | succ n ih =>
      intro omega eta hne
      by_cases htail : Fin.tail omega = Fin.tail eta
      · have hbit : omega 0 ≠ eta 0 := by
          intro hzero
          apply hne
          rw [← Fin.cons_self_tail omega, ← Fin.cons_self_tail eta, hzero, htail]
        cases homega : omega 0 <;> cases heta : eta 0
        · exact (hbit (by simp [homega, heta])).elim
        · left
          simpa [cantorStage_succ, homega, heta, htail] using
            (cantorTransition d n (Fin.tail omega)).separated
        · right
          simpa [cantorStage_succ, homega, heta, htail] using
            (cantorTransition d n (Fin.tail eta)).separated
        · exact (hbit (by simp [homega, heta])).elim
      · rcases ih (Fin.tail omega) (Fin.tail eta) htail with hparent | hparent
        · left
          have hnomega := cantorStage_nested d n omega
          have hneta := cantorStage_nested d n eta
          have hright :
              (cantorStage d (n + 1) omega).right <
                (cantorStage d n (Fin.tail omega)).right :=
            (hnomega (right_mem_Icc.mpr
              (cantorStage d (n + 1) omega).nondegenerate.le)).2
          have hleft :
              (cantorStage d n (Fin.tail eta)).left <
                (cantorStage d (n + 1) eta).left :=
            (hneta (left_mem_Icc.mpr
              (cantorStage d (n + 1) eta).nondegenerate.le)).1
          linarith
        · right
          have hnomega := cantorStage_nested d n omega
          have hneta := cantorStage_nested d n eta
          have hright :
              (cantorStage d (n + 1) eta).right <
                (cantorStage d n (Fin.tail eta)).right :=
            (hneta (right_mem_Icc.mpr
              (cantorStage d (n + 1) eta).nondegenerate.le)).2
          have hleft :
              (cantorStage d n (Fin.tail omega)).left <
                (cantorStage d (n + 1) omega).left :=
            (hnomega (left_mem_Icc.mpr
              (cantorStage d (n + 1) omega).nondegenerate.le)).1
          linarith

/-- A point belongs to at most one node interval at each depth. -/
theorem cantorStage_path_unique {f : ℝ → ℝ} (d : FusionInputs f)
    (n : ℕ) {omega eta : CantorPath n} {x : ℝ}
    (homega : x ∈ Icc (cantorStage d n omega).left (cantorStage d n omega).right)
    (heta : x ∈ Icc (cantorStage d n eta).left (cantorStage d n eta).right) :
    omega = eta := by
  by_contra hne
  rcases cantorStage_order_separated_of_ne d n omega eta hne with h | h
  · linarith [homega.2, heta.1]
  · linarith [heta.2, homega.1]

/-- The unique address containing a limit-set point at level n. -/
noncomputable def cantorPathAt {f : ℝ → ℝ} (d : FusionInputs f)
    (x : ℝ) (hx : x ∈ cantorLimitSet d) (n : ℕ) : CantorPath n :=
  Classical.choose (mem_iUnion.mp ((mem_iInter.mp hx) n))

theorem cantorPathAt_mem {f : ℝ → ℝ} (d : FusionInputs f)
    (x : ℝ) (hx : x ∈ cantorLimitSet d) (n : ℕ) :
    x ∈ Icc (cantorStage d n (cantorPathAt d x hx n)).left
            (cantorStage d n (cantorPathAt d x hx n)).right :=
  Classical.choose_spec (mem_iUnion.mp ((mem_iInter.mp hx) n))

/-- The level addresses of a limit-set point form a coherent branch. -/
theorem cantorPathAt_tail {f : ℝ → ℝ} (d : FusionInputs f)
    (x : ℝ) (hx : x ∈ cantorLimitSet d) (n : ℕ) :
    Fin.tail (cantorPathAt d x hx (n + 1)) = cantorPathAt d x hx n := by
  have hchild := cantorPathAt_mem d x hx (n + 1)
  have hparent_open :=
    cantorStage_nested d n (cantorPathAt d x hx (n + 1)) hchild
  have hparent :
      x ∈ Icc (cantorStage d n (Fin.tail (cantorPathAt d x hx (n + 1)))).left
              (cantorStage d n (Fin.tail (cantorPathAt d x hx (n + 1)))).right :=
    ⟨hparent_open.1.le, hparent_open.2.le⟩
  exact cantorStage_path_unique d n hparent (cantorPathAt_mem d x hx n)

/-- The coherent branch through a point, packaged in the existing fusion-data interface. -/
noncomputable def cantorBranchData {f : ℝ → ℝ} (d : FusionInputs f)
    (x : ℝ) (hx : x ∈ cantorLimitSet d) : FusionData f where
  left := fun n => (cantorStage d n (cantorPathAt d x hx n)).left
  right := fun n => (cantorStage d n (cantorPathAt d x hx n)).right
  interval_nonempty := fun n => (cantorStage d n (cantorPathAt d x hx n)).nondegenerate.le
  nested := by
    intro n y hy
    have h :=
      cantorStage_nested d n (cantorPathAt d x hx (n + 1)) hy
    rw [cantorPathAt_tail d x hx n] at h
    exact ⟨h.1.le, h.2.le⟩
  center := fun n => (cantorTransition d n (cantorPathAt d x hx n)).center
  center_den := by
    intro n
    exact le_trans
      (cantorTransition d n (cantorPathAt d x hx n)).height_ge_two
      (cantorTransition d n (cantorPathAt d x hx n)).den_lower
  cutoff := fun n => (cantorStage d n (cantorPathAt d x hx n)).cutoff
  cutoff_start := (cantorStage d 0 (cantorPathAt d x hx 0)).cutoff_ge_two
  cutoff_strict := strictMono_nat_of_lt_succ (fun n => by
    have h :=
      cantorStage_cutoff_growth d n (cantorPathAt d x hx (n + 1))
    rw [cantorPathAt_tail d x hx n] at h
    exact h)
  source_approx := by
    intro n y hy
    have h := cantorStage_source d n (cantorPathAt d x hx (n + 1)) y hy
    rw [cantorPathAt_tail d x hx n] at h
    exact h
  target_avoid := by
    intro n y hy a b hlo hhi
    have h := cantorStage_target d n (cantorPathAt d x hx (n + 1))
      y hy a b
    rw [cantorPathAt_tail d x hx n] at h
    exact h hlo hhi

/-- Every point of the binary limit set is Liouville. -/
theorem cantorLimitSet_liouville {f : ℝ → ℝ} (d : FusionInputs f)
    {x : ℝ} (hx : x ∈ cantorLimitSet d) :
    Liouville x := by
  let bd := cantorBranchData d x hx
  exact liouville_of_source_approximations x bd.center bd.center_den
    (fun n => bd.source_approx n x (cantorPathAt_mem d x hx (n + 1)))

/-- One root cutoff works for target avoidance at every point of the limit set. -/
theorem cantorLimitSet_target_avoidance {f : ℝ → ℝ} (d : FusionInputs f)
    {x : ℝ} (hx : x ∈ cantorLimitSet d) :
    EventualTargetAvoidance (f x) 100 (initialFusionStage d).cutoff := by
  let bd := cantorBranchData d x hx
  have havoid : EventualTargetAvoidance (f x) 100 (bd.cutoff 0) :=
    target_avoidance_from_blocks (f x) 100 bd.cutoff bd.cutoff_strict
      (fun n => bd.target_avoid n x (cantorPathAt_mem d x hx (n + 1)))
  simpa [bd, cantorBranchData, cantorStage] using havoid

/-- Hence every image point has irrationality exponent at most 100. -/
theorem cantorLimitSet_irrationalityExponent_le {f : ℝ → ℝ} (d : FusionInputs f)
    {x : ℝ} (hx : x ∈ cantorLimitSet d) :
    irrationalityExponent (f x) ≤ (100 : EReal) :=
  irrationalityExponent_le_of_eventual_target_avoidance
    (cantorLimitSet_target_avoidance d hx)

end MahlerLean
