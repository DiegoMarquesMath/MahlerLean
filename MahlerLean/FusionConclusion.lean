import MahlerLean.LiouvilleBridge
import MahlerLean.CountingToSafeCenter

/-!
The final implication in Section 6: nested intervals satisfying the source
and target invariants yield a Liouville escape point.

No sequence of intervals is constructed here. FusionData explicitly records
the geometric and arithmetic data that a later construction must produce.
The analytic hypotheses of the paper must eventually be used to build it.
-/

namespace MahlerLean

open Set

/-- Consecutive blocks of a strictly increasing natural sequence cover
all integers from its initial value onwards. -/
theorem exists_target_block (T : ℕ → ℕ) (hT : StrictMono T)
    (b : ℕ) (hb : T 0 ≤ b) :
    ∃ n : ℕ, T n ≤ b ∧ b < T (n + 1) := by
  have hgrowth : ∀ n : ℕ, n ≤ T n := by
    intro n
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih =>
      exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (hT (Nat.lt_succ_self n)))
  have hex : ∃ k : ℕ, b < T k :=
    ⟨b + 1, lt_of_lt_of_le (Nat.lt_succ_self b) (hgrowth (b + 1))⟩
  have hk : b < T (Nat.find hex) := Nat.find_spec hex
  have hkpos : 0 < Nat.find hex := by
    by_contra h
    have hkzero : Nat.find hex = 0 := by omega
    rw [hkzero] at hk
    omega
  have hprev : ¬ b < T (Nat.find hex - 1) := Nat.find_min hex (by omega)
  refine ⟨Nat.find hex - 1, by omega, ?_⟩
  have heq : Nat.find hex - 1 + 1 = Nat.find hex := by omega
  simpa only [heq] using hk

/-- Blockwise avoidance yields one eventual bound for every target
numerator and every denominator above the initial cutoff. -/
theorem target_avoidance_from_blocks
    (y : ℝ) (tau : ℕ) (T : ℕ → ℕ) (hT : StrictMono T)
    (hblocks : ∀ n : ℕ, ∀ a : ℤ, ∀ b : ℕ,
      T n ≤ b → b < T (n + 1) →
      ((b : ℝ) ^ tau)⁻¹ < |y - (a : ℝ) / (b : ℝ)|) :
    EventualTargetAvoidance y tau (T 0) := by
  intro a b hb
  obtain ⟨n, hnlo, hnhi⟩ := exists_target_block T hT b hb
  exact hblocks n a b hnlo hnhi

/-- The data and invariants used by the concluding part of fusion.
This structure is a hypothesis package, not an assertion that such data
exist for any analytic function. Nestedness is stated in the weaker form
of closed-interval inclusion, which suffices for this final implication. -/
structure FusionData (f : ℝ → ℝ) where
  left : ℕ → ℝ
  right : ℕ → ℝ
  interval_nonempty : ∀ n, left n ≤ right n
  nested : ∀ n, Icc (left (n + 1)) (right (n + 1)) ⊆ Icc (left n) (right n)
  center : ℕ → ℚ
  center_den : ∀ n, 2 ≤ (center n).den
  cutoff : ℕ → ℕ
  cutoff_start : 2 ≤ cutoff 0
  cutoff_strict : StrictMono cutoff
  source_approx : ∀ n, ∀ x ∈ Icc (left (n + 1)) (right (n + 1)),
    0 < |x - (center n : ℝ)| ∧
    |x - (center n : ℝ)| < (((center n).den : ℝ) ^ (n + 3))⁻¹
  target_avoid : ∀ n, ∀ x ∈ Icc (left (n + 1)) (right (n + 1)),
    ∀ a : ℤ, ∀ b : ℕ, cutoff n ≤ b → b < cutoff (n + 1) →
    ((b : ℝ) ^ 100)⁻¹ < |f x - (a : ℝ) / (b : ℝ)|

/-- The concluding implication of Section 6, conditional on FusionData.
The point lies in every interval, is Liouville in both equivalent
conventions, and its image has the explicit eventual lower bound
b^(-100). In particular, its image is not Liouville. -/
theorem exists_escape_of_fusion_data (f : ℝ → ℝ) (d : FusionData f) :
    ∃ x : ℝ, (∀ n, x ∈ Icc (d.left n) (d.right n)) ∧
      Liouville x ∧ PaperLiouville x ∧
      EventualTargetAvoidance (f x) 100 (d.cutoff 0) ∧ ¬ Liouville (f x) := by
  obtain ⟨x, hx⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      (fun n => Icc (d.left n) (d.right n)) d.nested
      (fun n => nonempty_Icc.mpr (d.interval_nonempty n))
      isCompact_Icc (fun _ => isClosed_Icc)
  have hmem : ∀ n, x ∈ Icc (d.left n) (d.right n) := mem_iInter.mp hx
  have hL : Liouville x := liouville_of_source_approximations x d.center d.center_den
    (fun n => d.source_approx n x (hmem (n + 1)))
  have havoid : EventualTargetAvoidance (f x) 100 (d.cutoff 0) :=
    target_avoidance_from_blocks (f x) 100 d.cutoff d.cutoff_strict
      (fun n => d.target_avoid n x (hmem (n + 1)))
  exact ⟨x, hmem, hL, (liouville_iff_paperLiouville x).mp hL, havoid,
    not_liouville_of_eventual_target_avoidance (f x) 100 (d.cutoff 0) havoid⟩

/-- The mean-value step used to transfer a safe center to nearby points.
The derivative bound now supplies the movement estimate required by the
previous update. Selecting an interval that also preserves the other
fusion invariants remains a separate task. -/
theorem safeCenter_avoidance_of_deriv_bound
    (f : ℝ → ℝ) (l u M : ℝ) (Q A H : ℕ) (r : ℚ) (x : ℝ)
    (hM : 0 ≤ M) (hsafe : IsSafeCenter f M Q A H r)
    (hf : ∀ y ∈ Icc l u, DifferentiableAt ℝ f y)
    (hderiv : ∀ y ∈ Icc l u, |deriv f y| ≤ M)
    (hr : (r : ℝ) ∈ Icc l u) (hx : x ∈ Icc l u)
    (hclose : |x - (r : ℝ)| ≤ ((Q : ℝ) ^ A)⁻¹) :
    ∀ a : ℤ, ∀ b : ℕ, 0 < b → H ≤ b → (b : ℝ) < targetCutoff Q A →
      ((b : ℝ) ^ 100)⁻¹ < |f x - (a : ℝ) / (b : ℝ)| := by
  have hmv : |f x - f (r : ℝ)| ≤ M * |x - (r : ℝ)| := by
    simpa only [Real.norm_eq_abs] using
      Convex.norm_image_sub_le_of_norm_deriv_le hf
        (fun y hy => by simpa only [Real.norm_eq_abs] using hderiv y hy)
        (convex_Icc l u) hr hx
  have hmove : |f x - f (r : ℝ)| ≤ M * ((Q : ℝ) ^ A)⁻¹ :=
    hmv.trans (mul_le_mul_of_nonneg_left hclose hM)
  exact safeCenter_avoidance_of_movement f M Q A H r x hM hsafe hmove

end MahlerLean
