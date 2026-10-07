import MahlerLean.CantorFusion
import Mathlib.Data.Fin.Tuple.Basic

/-!
The binary fusion tree and its compact level sets.

A node at depth n is indexed by a Boolean n-tuple. We store the newest
choice at coordinate zero, so the parent of omega : Fin (n+1) -> Bool
is Fin.tail omega. This convention makes primitive recursion on the
depth definitionally simple.
-/

noncomputable section
namespace MahlerLean

open Set

/-- Binary addresses of nodes at depth n. -/
abbrev CantorPath (n : ℕ) := Fin n → Bool

/-- The fusion stage attached to a binary address. -/
noncomputable def cantorStage {f : ℝ → ℝ} (d : FusionInputs f) :
    (n : ℕ) → CantorPath n → FusionStage d n
  | 0, _ => initialFusionStage d
  | n + 1, omega =>
      let parent := cantorStage d n (Fin.tail omega)
      let t := Classical.choice (exists_binary_fusion_transition d n parent)
      if omega 0 then t.rightChild else t.leftChild

/-- The chosen binary transition at a node. -/
noncomputable def cantorTransition {f : ℝ → ℝ} (d : FusionInputs f)
    (n : ℕ) (omega : CantorPath n) :
    BinaryFusionTransition d n (cantorStage d n omega) :=
  Classical.choice (exists_binary_fusion_transition d n (cantorStage d n omega))

theorem cantorStage_succ {f : ℝ → ℝ} (d : FusionInputs f)
    (n : ℕ) (omega : CantorPath (n + 1)) :
    cantorStage d (n + 1) omega =
      if omega 0 then
        (cantorTransition d n (Fin.tail omega)).rightChild
      else
        (cantorTransition d n (Fin.tail omega)).leftChild := rfl

@[simp]
theorem cantorStage_cons_false {f : ℝ → ℝ} (d : FusionInputs f)
    (n : ℕ) (omega : CantorPath n) :
    cantorStage d (n + 1) (Fin.cons false omega) =
      (cantorTransition d n omega).leftChild := by
  rw [cantorStage_succ]
  have htail : Fin.tail (Fin.cons false omega) = omega := by
    funext i
    simp [Fin.tail]
  rw [htail]
  simp

@[simp]
theorem cantorStage_cons_true {f : ℝ → ℝ} (d : FusionInputs f)
    (n : ℕ) (omega : CantorPath n) :
    cantorStage d (n + 1) (Fin.cons true omega) =
      (cantorTransition d n omega).rightChild := by
  rw [cantorStage_succ]
  have htail : Fin.tail (Fin.cons true omega) = omega := by
    funext i
    simp [Fin.tail]
  rw [htail]
  simp

/-- Every child interval lies strictly inside its parent interval. -/
theorem cantorStage_nested {f : ℝ → ℝ} (d : FusionInputs f)
    (n : ℕ) (omega : CantorPath (n + 1)) :
    Icc (cantorStage d (n + 1) omega).left
        (cantorStage d (n + 1) omega).right ⊆
      Ioo (cantorStage d n (Fin.tail omega)).left
          (cantorStage d n (Fin.tail omega)).right := by
  rw [cantorStage_succ]
  by_cases h : omega 0
  · simp only [h]
    exact (cantorTransition d n (Fin.tail omega)).right_nested
  · simp only [h]
    exact (cantorTransition d n (Fin.tail omega)).left_nested

/-- The target cutoff grows strictly along every edge of the tree. -/
theorem cantorStage_cutoff_growth {f : ℝ → ℝ} (d : FusionInputs f)
    (n : ℕ) (omega : CantorPath (n + 1)) :
    (cantorStage d n (Fin.tail omega)).cutoff <
      (cantorStage d (n + 1) omega).cutoff := by
  rw [cantorStage_succ]
  by_cases h : omega 0
  · simp only [h]
    exact (cantorTransition d n (Fin.tail omega)).cutoff_growth_right
  · simp only [h]
    exact (cantorTransition d n (Fin.tail omega)).cutoff_growth_left

/-- Source approximation inherited by every child. -/
theorem cantorStage_source {f : ℝ → ℝ} (d : FusionInputs f)
    (n : ℕ) (omega : CantorPath (n + 1))
    (x : ℝ)
    (hx : x ∈ Icc (cantorStage d (n + 1) omega).left
                    (cantorStage d (n + 1) omega).right) :
    let t := cantorTransition d n (Fin.tail omega)
    0 < |x - (t.center : ℝ)| ∧
      |x - (t.center : ℝ)| <
        (((t.center.den : ℕ) : ℝ) ^ (n + 3))⁻¹ := by
  rw [cantorStage_succ] at hx
  by_cases h : omega 0
  · simp only [h] at hx
    exact (cantorTransition d n (Fin.tail omega)).source_right x hx
  · simp only [h] at hx
    exact (cantorTransition d n (Fin.tail omega)).source_left x hx

/-- Target avoidance inherited by every child. -/
theorem cantorStage_target {f : ℝ → ℝ} (d : FusionInputs f)
    (n : ℕ) (omega : CantorPath (n + 1))
    (x : ℝ)
    (hx : x ∈ Icc (cantorStage d (n + 1) omega).left
                    (cantorStage d (n + 1) omega).right)
    (a : ℤ) (b : ℕ)
    (hlo : (cantorStage d n (Fin.tail omega)).cutoff ≤ b)
    (hhi : b < (cantorStage d (n + 1) omega).cutoff) :
    ((b : ℝ) ^ 100)⁻¹ < |f x - (a : ℝ) / (b : ℝ)| := by
  rw [cantorStage_succ] at hx hhi
  by_cases h : omega 0
  · simp only [h] at hx hhi
    exact (cantorTransition d n (Fin.tail omega)).target_right x hx a b hlo hhi
  · simp only [h] at hx hhi
    exact (cantorTransition d n (Fin.tail omega)).target_left x hx a b hlo hhi

/-- The two children of a node are strictly separated. -/
theorem cantorStage_siblings_separated {f : ℝ → ℝ} (d : FusionInputs f)
    (n : ℕ) (omega : CantorPath n) :
    (cantorStage d (n + 1) (Fin.cons false omega)).right <
      (cantorStage d (n + 1) (Fin.cons true omega)).left := by
  simp only [cantorStage_cons_false, cantorStage_cons_true]
  exact (cantorTransition d n omega).separated

/-- Compact union of all intervals at one depth. -/
def cantorLevel {f : ℝ → ℝ} (d : FusionInputs f) (n : ℕ) : Set ℝ :=
  ⋃ omega : CantorPath n,
    Icc (cantorStage d n omega).left (cantorStage d n omega).right

theorem cantorLevel_compact {f : ℝ → ℝ} (d : FusionInputs f) (n : ℕ) :
    IsCompact (cantorLevel d n) := by
  unfold cantorLevel
  exact isCompact_iUnion fun _ => isCompact_Icc

theorem cantorLevel_nonempty {f : ℝ → ℝ} (d : FusionInputs f) (n : ℕ) :
    (cantorLevel d n).Nonempty := by
  let omega : CantorPath n := fun _ => false
  have hnon :
      (Icc (cantorStage d n omega).left (cantorStage d n omega).right).Nonempty :=
    nonempty_Icc.mpr (cantorStage d n omega).nondegenerate.le
  exact hnon.mono (subset_iUnion (fun eta : CantorPath n =>
    Icc (cantorStage d n eta).left (cantorStage d n eta).right) omega)

theorem cantorLevel_nested {f : ℝ → ℝ} (d : FusionInputs f) (n : ℕ) :
    cantorLevel d (n + 1) ⊆ cantorLevel d n := by
  intro x hx
  rcases mem_iUnion.mp hx with ⟨omega, homega⟩
  have hp : x ∈ Icc (cantorStage d n (Fin.tail omega)).left
                    (cantorStage d n (Fin.tail omega)).right := by
    have h := cantorStage_nested d n omega homega
    exact ⟨h.1.le, h.2.le⟩
  exact mem_iUnion.mpr ⟨Fin.tail omega, hp⟩

/-- The compact limit set of the full binary fusion tree. -/
def cantorLimitSet {f : ℝ → ℝ} (d : FusionInputs f) : Set ℝ :=
  ⋂ n : ℕ, cantorLevel d n

theorem cantorLimitSet_nonempty {f : ℝ → ℝ} (d : FusionInputs f) :
    (cantorLimitSet d).Nonempty := by
  unfold cantorLimitSet
  exact IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun n => cantorLevel d n)
    (cantorLevel_nested d)
    (cantorLevel_nonempty d)
    (cantorLevel_compact d 0)
    (fun n => (cantorLevel_compact d n).isClosed)

theorem cantorLimitSet_compact {f : ℝ → ℝ} (d : FusionInputs f) :
    IsCompact (cantorLimitSet d) := by
  have hclosed : IsClosed (cantorLimitSet d) := by
    unfold cantorLimitSet
    exact isClosed_iInter fun n => (cantorLevel_compact d n).isClosed
  have hsub : cantorLimitSet d ⊆ cantorLevel d 0 := by
    unfold cantorLimitSet
    exact iInter_subset _ 0
  exact (cantorLevel_compact d 0).of_isClosed_subset hclosed hsub

theorem cantorLimitSet_subset_ambient {f : ℝ → ℝ} (d : FusionInputs f) :
    cantorLimitSet d ⊆ Ioo d.left d.right := by
  intro x hx
  have hx0 : x ∈ cantorLevel d 0 := (mem_iInter.mp hx) 0
  rcases mem_iUnion.mp hx0 with ⟨omega, homega⟩
  exact (cantorStage d 0 omega).contained homega

end MahlerLean
