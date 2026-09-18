import MahlerLean.FusionStep

/-!
Initialization and infinite recursion for fusion, conditional on explicit
counting and source-supply hypotheses on compact subintervals. The constants
M, Clow and cF and the sequence of finite forbidden sets are fixed before
recursion. The remainder constant and counting threshold may depend on the
interval and stage, but not on the lower target cutoff.

The analytic derivation of these inputs is not proved in this module.
-/

namespace MahlerLean

open Set

/-- The local analytic/counting interface required by the recursion.
The fields assert estimates, not the existence of safe centers or fusion
data. In the intended application, zeros n contains the relevant Wronskian
zeros at exponent n+3. That interpretation remains to be formalized. -/
structure FusionInputs (f : ℝ → ℝ) where
  left : ℝ
  right : ℝ
  nondegenerate : left < right
  M : ℝ
  Clow : ℝ
  cF : ℝ
  M_nonneg : 0 ≤ M
  Clow_nonneg : 0 ≤ Clow
  cF_pos : 0 < cF
  differentiable : ∀ x ∈ Icc left right, DifferentiableAt ℝ f x
  deriv_bound : ∀ x ∈ Icc left right, |deriv f x| ≤ M
  zeros : ℕ → Finset ℝ
  supply : ∀ l u : ℝ, l < u → Icc l u ⊆ Icc left right →
    HasSourceSupply l u cF
  counting : ∀ n : ℕ, ∀ l u : ℝ, l < u → Icc l u ⊆ Icc left right →
    (∀ x ∈ Icc l u, x ∉ zeros n) →
    ∃ C : ℝ, HasUniformDangerBound f l u M Clow C (n + 3)

/-- A sufficiently large initial target cutoff satisfies the tail bound
on any interval of positive length. -/
theorem exists_initial_tail_cutoff (Clow cF l u : ℝ)
    (hcF : 0 < cF) (hlu : l < u) :
    ∃ H : ℕ, 2 ≤ H ∧
      Clow * ((H : ℝ) ^ 98)⁻¹ ≤ (cF / 4) * ((u - l) / 3) := by
  have hwidth : 0 < u - l := sub_pos.mpr hlu
  have hpos : 0 < (cF / 4) * ((u - l) / 3) := by positivity
  have hlim : Filter.Tendsto (fun H : ℕ => Clow * ((H : ℝ) ^ 98)⁻¹)
      Filter.atTop (nhds 0) := by
    have hp : Filter.Tendsto (fun H : ℕ => ((H : ℝ) ^ 98)⁻¹)
        Filter.atTop (nhds 0) := by
      simpa only [Function.comp_def, Real.rpow_neg (Nat.cast_nonneg _),
        Real.rpow_natCast] using
        (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < (98 : ℕ))).comp
          tendsto_natCast_atTop_atTop
    simpa using hp.const_mul Clow
  have hevent : ∀ᶠ H : ℕ in Filter.atTop, 2 ≤ H ∧
      Clow * ((H : ℝ) ^ 98)⁻¹ ≤ (cF / 4) * ((u - l) / 3) :=
    (Filter.eventually_ge_atTop (2 : ℕ)).and (hlim.eventually_le_const hpos)
  exact hevent.exists

/-- The invariants needed when entering stage n. previousDen carries the
preceding center's denominator; at stage zero it is set to zero. -/
structure FusionStage {f : ℝ → ℝ} (d : FusionInputs f) (n : ℕ) where
  left : ℝ
  right : ℝ
  nondegenerate : left < right
  contained : Icc left right ⊆ Ioo d.left d.right
  avoids : ∀ x ∈ Icc left right, x ∉ d.zeros n
  cutoff : ℕ
  cutoff_ge_two : 2 ≤ cutoff
  tail : d.Clow * ((cutoff : ℝ) ^ 98)⁻¹ ≤ (d.cF / 4) * ((right - left) / 3)
  previousDen : ℕ

/-- Initial interval and cutoff, before any safe center is selected. -/
theorem exists_initial_fusion_stage {f : ℝ → ℝ} (d : FusionInputs f) :
    Nonempty (FusionStage d 0) := by
  obtain ⟨l, u, hl, hlu, hu, _hlen, havoid⟩ :=
    exists_interval_avoiding_finset (d.zeros 0) d.left d.right
      ((d.zeros 0).card + 1) d.nondegenerate (by omega)
  obtain ⟨H, hH, htail⟩ := exists_initial_tail_cutoff d.Clow d.cF l u d.cF_pos hlu
  exact ⟨{
    left := l
    right := u
    nondegenerate := hlu
    contained := fun _ hx => ⟨hl.trans_le hx.1, hx.2.trans_lt hu⟩
    avoids := havoid
    cutoff := H
    cutoff_ge_two := hH
    tail := htail
    previousDen := 0 }⟩

/-- A chosen scale and center, together with all proofs for the next
interval. This is obtained from successor_from_counting, not postulated. -/
structure FusionTransition {f : ℝ → ℝ} (d : FusionInputs f) (n : ℕ)
    (s : FusionStage d n) where
  height : ℕ
  height_ge_two : 2 ≤ height
  height_growth : 2 * s.previousDen < height
  center : ℚ
  den_lower : height ≤ center.den
  den_upper : center.den < 2 * height
  interval : SuccessorInterval f (d.zeros (n + 1)) s.left s.right
    d.Clow d.cF height (n + 3) s.cutoff center

/-- Every stage has a successor. Supply and counting are applied on its
middle third. The next forbidden set is fixed before the scale is chosen. -/
theorem exists_fusion_transition {f : ℝ → ℝ} (d : FusionInputs f)
    (n : ℕ) (s : FusionStage d n) : Nonempty (FusionTransition d n s) := by
  let l := s.left + (s.right - s.left) / 3
  let u := s.right - (s.right - s.left) / 3
  have hlu : l < u := by dsimp [l, u]; linarith [s.nondegenerate]
  have hmid : Icc l u ⊆ Icc s.left s.right := by
    intro x hx
    dsimp [l, u] at hx
    constructor <;> linarith [s.nondegenerate, hx.1, hx.2]
  have hparent : Icc s.left s.right ⊆ Icc d.left d.right := by
    intro x hx
    exact ⟨(s.contained hx).1.le, (s.contained hx).2.le⟩
  have hambient : Icc l u ⊆ Icc d.left d.right := hmid.trans hparent
  obtain ⟨C, hC⟩ := d.counting n l u hlu hambient (fun x hx => s.avoids x (hmid hx))
  obtain ⟨Q, hmin, hQ, r, hlo, hhi, hi⟩ :=
    successor_from_counting f (d.zeros (n + 1)) s.left s.right
      d.M d.Clow d.cF C (n + 3) s.cutoff (2 * s.previousDen + 1)
      s.nondegenerate (by omega) s.cutoff_ge_two d.M_nonneg d.Clow_nonneg d.cF_pos
      (fun x hx => d.differentiable x (hparent hx))
      (fun x hx => d.deriv_bound x (hparent hx))
      (d.supply l u hlu hambient) hC s.tail
  exact ⟨{
    height := Q
    height_ge_two := hQ
    height_growth := by omega
    center := r
    den_lower := hlo
    den_upper := hhi
    interval := Classical.choice hi }⟩

/-- A transition carries all the invariants needed by the next stage. -/
noncomputable def FusionTransition.nextStage {f : ℝ → ℝ} {d : FusionInputs f}
    {n : ℕ} {s : FusionStage d n} (t : FusionTransition d n s) :
    FusionStage d (n + 1) where
  left := t.interval.left
  right := t.interval.right
  nondegenerate := t.interval.nondegenerate
  contained := fun _ hx => s.contained
    ⟨(t.interval.nested hx).1.le, (t.interval.nested hx).2.le⟩
  avoids := t.interval.avoids
  cutoff := nextCutoff t.height (n + 3)
  cutoff_ge_two := le_trans s.cutoff_ge_two t.interval.cutoff_increases.le
  tail := t.interval.tail
  previousDen := t.center.den

noncomputable def initialFusionStage {f : ℝ → ℝ} (d : FusionInputs f) :
    FusionStage d 0 := Classical.choice (exists_initial_fusion_stage d)

noncomputable def chooseFusionTransition {f : ℝ → ℝ} (d : FusionInputs f)
    (n : ℕ) (s : FusionStage d n) : FusionTransition d n s :=
  Classical.choice (exists_fusion_transition d n s)

/-- Primitive recursion with a stage type indexed by n. -/
noncomputable def fusionStages {f : ℝ → ℝ} (d : FusionInputs f) :
    (n : ℕ) → FusionStage d n
  | 0 => initialFusionStage d
  | n + 1 => (chooseFusionTransition d n (fusionStages d n)).nextStage

/-- The exact successor equation used to transfer the local invariants
to the infinite sequence. -/
theorem fusionStages_succ {f : ℝ → ℝ} (d : FusionInputs f) (n : ℕ) :
    fusionStages d (n + 1) =
      (chooseFusionTransition d n (fusionStages d n)).nextStage := rfl

/-- FusionData together with the additional invariants of the actual
construction: strict nesting, forbidden-set avoidance, denominator growth
and the tail condition at every stage. -/
structure FusionConstruction {f : ℝ → ℝ} (d : FusionInputs f) extends FusionData f where
  interval_positive : ∀ n, left n < right n
  contained : ∀ n, Icc (left n) (right n) ⊆ Ioo d.left d.right
  nested_interior : ∀ n, Icc (left (n + 1)) (right (n + 1)) ⊆ Ioo (left n) (right n)
  avoids : ∀ n, ∀ x ∈ Icc (left n) (right n), x ∉ d.zeros n
  denominator_growth : ∀ n, 2 * (center n).den < (center (n + 1)).den
  tail : ∀ n, d.Clow * ((cutoff n : ℝ) ^ 98)⁻¹ ≤
    (d.cF / 4) * ((right n - left n) / 3)

/-- Assemble the infinite sequence with all seven fusion invariants.
The explicit counting interface replaces assumptions of preexisting
intervals; it has not yet been derived from the analytic hypotheses. -/
noncomputable def fusionConstruction {f : ℝ → ℝ} (d : FusionInputs f) :
    FusionConstruction d where
  left := fun n => (fusionStages d n).left
  right := fun n => (fusionStages d n).right
  interval_nonempty := fun n => (fusionStages d n).nondegenerate.le
  nested := by
    intro n x hx
    have h := (chooseFusionTransition d n (fusionStages d n)).interval.nested hx
    exact ⟨h.1.le, h.2.le⟩
  center := fun n => (chooseFusionTransition d n (fusionStages d n)).center
  center_den := fun n => le_trans
    (chooseFusionTransition d n (fusionStages d n)).height_ge_two
    (chooseFusionTransition d n (fusionStages d n)).den_lower
  cutoff := fun n => (fusionStages d n).cutoff
  cutoff_start := (fusionStages d 0).cutoff_ge_two
  cutoff_strict := strictMono_nat_of_lt_succ (fun n =>
    (chooseFusionTransition d n (fusionStages d n)).interval.cutoff_increases)
  source_approx := fun n => (chooseFusionTransition d n (fusionStages d n)).interval.source
  target_avoid := fun n => (chooseFusionTransition d n (fusionStages d n)).interval.target
  interval_positive := fun n => (fusionStages d n).nondegenerate
  contained := fun n => (fusionStages d n).contained
  nested_interior := fun n => (chooseFusionTransition d n (fusionStages d n)).interval.nested
  avoids := fun n => (fusionStages d n).avoids
  denominator_growth := fun n => lt_of_lt_of_le
    (chooseFusionTransition d (n + 1) (fusionStages d (n + 1))).height_growth
    (chooseFusionTransition d (n + 1) (fusionStages d (n + 1))).den_lower
  tail := fun n => (fusionStages d n).tail

/-- Existence of an infinite construction with all recorded invariants. -/
theorem exists_fusion_construction {f : ℝ → ℝ} (d : FusionInputs f) :
    Nonempty (FusionConstruction d) := ⟨fusionConstruction d⟩

end MahlerLean
