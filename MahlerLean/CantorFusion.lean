import MahlerLean.FusionRecursion

/-!
Binary refinement of the fusion construction.

The single-branch construction chooses one interval after deleting the
next finite Wronskian-zero set and the current rational center.  For the
Cantor refinement we first choose the same safe center and a slightly
stronger scale, then split one admissible interval into two separated
closed thirds.  Both children inherit the source approximation and target
avoidance estimates.  The stronger scale is only a constant-factor change
in the tail budget.
-/

noncomputable section
namespace MahlerLean

open Set

/-- Two admissible children of one fusion stage, sharing the same safe
center, source height and next target cutoff. -/
structure BinaryFusionTransition {f : ℝ → ℝ} (d : FusionInputs f) (n : ℕ)
    (s : FusionStage d n) where
  height : ℕ
  height_ge_two : 2 ≤ height
  height_growth : 2 * s.previousDen < height
  center : ℚ
  den_lower : height ≤ center.den
  den_upper : center.den < 2 * height
  leftChild : FusionStage d (n + 1)
  rightChild : FusionStage d (n + 1)
  left_nested : Icc leftChild.left leftChild.right ⊆ Ioo s.left s.right
  right_nested : Icc rightChild.left rightChild.right ⊆ Ioo s.left s.right
  separated : leftChild.right < rightChild.left
  left_cutoff : leftChild.cutoff = nextCutoff height (n + 3)
  right_cutoff : rightChild.cutoff = nextCutoff height (n + 3)
  cutoff_growth_left : s.cutoff < leftChild.cutoff
  cutoff_growth_right : s.cutoff < rightChild.cutoff
  left_previousDen : leftChild.previousDen = center.den
  right_previousDen : rightChild.previousDen = center.den
  source_left : ∀ x ∈ Icc leftChild.left leftChild.right,
    0 < |x - (center : ℝ)| ∧
      |x - (center : ℝ)| < (((center.den : ℕ) : ℝ) ^ (n + 3))⁻¹
  source_right : ∀ x ∈ Icc rightChild.left rightChild.right,
    0 < |x - (center : ℝ)| ∧
      |x - (center : ℝ)| < (((center.den : ℕ) : ℝ) ^ (n + 3))⁻¹
  target_left : ∀ x ∈ Icc leftChild.left leftChild.right,
    ∀ a : ℤ, ∀ b : ℕ, s.cutoff ≤ b → b < leftChild.cutoff →
      ((b : ℝ) ^ 100)⁻¹ < |f x - (a : ℝ) / (b : ℝ)|
  target_right : ∀ x ∈ Icc rightChild.left rightChild.right,
    ∀ a : ℤ, ∀ b : ℕ, s.cutoff ≤ b → b < rightChild.cutoff →
      ((b : ℝ) ^ 100)⁻¹ < |f x - (a : ℝ) / (b : ℝ)|

/-- A closed interval split into its left and right thirds gives two
strictly separated nondegenerate children. -/
theorem split_interval_thirds
    (a b : ℝ) (hab : a < b) :
    let w := (b - a) / 3
    a < a + w ∧
    a + 2 * w < b ∧
    a + w < a + 2 * w ∧
    Icc a (a + w) ⊆ Icc a b ∧
    Icc (a + 2 * w) b ⊆ Icc a b ∧
    (a + w) - a = w ∧
    b - (a + 2 * w) = w := by
  dsimp
  have hw : 0 < (b - a) / 3 := by linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · intro x hx
    exact ⟨hx.1, by linarith [hx.2]⟩
  constructor
  · intro x hx
    exact ⟨by linarith [hx.1], hx.2⟩
  constructor <;> ring

/-- Every fusion stage has two separated successors.  Relative to the
single-branch step, the only stronger requirement is the constant factor
in the tail budget needed after taking thirds. -/
theorem exists_binary_fusion_transition {f : ℝ → ℝ} (d : FusionInputs f)
    (n : ℕ) (s : FusionStage d n) :
    Nonempty (BinaryFusionTransition d n s) := by
  let l := s.left + (s.right - s.left) / 3
  let u := s.right - (s.right - s.left) / 3
  have hlu : l < u := by
    dsimp [l, u]
    linarith [s.nondegenerate]
  have hmid : Icc l u ⊆ Icc s.left s.right := by
    intro x hx
    dsimp [l, u] at hx
    constructor <;> linarith [s.nondegenerate, hx.1, hx.2]
  have hparent : Icc s.left s.right ⊆ Icc d.left d.right := by
    intro x hx
    exact ⟨(s.contained hx).1.le, (s.contained hx).2.le⟩
  have hambient : Icc l u ⊆ Icc d.left d.right := hmid.trans hparent
  obtain ⟨C, hC⟩ :=
    d.counting n l u hlu hambient (fun x hx => s.avoids x (hmid hx))
  obtain ⟨Qs, _hQs, hs⟩ := safe_center_of_counting_estimates f
    l u d.M d.cF d.Clow C (n + 3) hlu d.cF_pos
      (d.supply l u hlu hambient) hC
  let Z := d.zeros (n + 1)
  let Lambda : ℕ := Z.card + 2
  have hLambda : 0 < Lambda := by
    dsimp [Lambda]
    omega
  obtain ⟨Q, hmin, hQ, hfit, hheight, hscale⟩ :=
    exists_large_fusion_scale (n + 3) s.cutoff (3 * Lambda)
      (max (2 * s.previousDen + 1) Qs) d.Clow d.cF
      ((s.right - s.left) / 3)
      (by omega) d.cF_pos (by linarith [s.nondegenerate])
  have htailmid : d.Clow * ((s.cutoff : ℝ) ^ 98)⁻¹ ≤
      d.cF * ((u - l)) / 4 := by
    rw [middle_third_length]
    nlinarith [s.tail]
  obtain ⟨r, hrl, hru, hdenlo, hdenhi, hsafe⟩ :=
    hs s.cutoff s.cutoff_ge_two htailmid Q (by omega)
  let R := fusionRadius Q (n + 3)
  have hRpos : 0 < R := by
    dsimp [R, fusionRadius]
    positivity
  have hrleft : s.left + (s.right - s.left) / 3 ≤ (r : ℝ) := by
    simpa [l] using hrl
  have hrright : (r : ℝ) ≤ s.right - (s.right - s.left) / 3 := by
    simpa [u] using hru
  obtain ⟨a, b, hab, habsub, hlen, havoid⟩ :=
    exists_next_interval_in_parent Z s.left s.right (r : ℝ) R hRpos
      hrleft hrright hfit
  let w : ℝ := (b - a) / 3
  have hsplit := split_interval_thirds a b hab
  dsimp only at hsplit
  rcases hsplit with
    ⟨hleftpos, hrightpos, hsep, hleftsub, hrightsub, hleftlen, hrightlen⟩
  have hnext : s.cutoff < nextCutoff Q (n + 3) :=
    nextCutoff_gt Q (n + 3) s.cutoff hheight
  have hnext_two : 2 ≤ nextCutoff Q (n + 3) :=
    le_trans s.cutoff_ge_two hnext.le
  have hstrongtail :
      d.Clow * (((nextCutoff Q (n + 3) : ℕ) : ℝ) ^ 98)⁻¹ ≤
        (d.cF / 4) * (R / (3 * ((3 * Lambda : ℕ) : ℝ))) := by
    exact tail_smallness_next Q (n + 3) (3 * Lambda) d.Clow d.cF
      (by omega) (by omega) d.Clow_nonneg
      (by
        have : (2 : ℝ) * s.cutoff + 2 ≤ targetCutoff Q (n + 3) := by
          simpa only [Nat.cast_ofNat, Nat.cast_mul, Nat.cast_add] using hheight
        linarith)
      hscale
  have hchildtail :
      d.Clow * (((nextCutoff Q (n + 3) : ℕ) : ℝ) ^ 98)⁻¹ ≤
        (d.cF / 4) * (w / 3) := by
    have hLambdaR : (0 : ℝ) < Lambda := by exact_mod_cast hLambda
    have hlen' : b - a = R / (Lambda : ℝ) := by
      simpa [Z, Lambda] using hlen
    have hw : w = R / (3 * (Lambda : ℝ)) := by
      dsimp [w]
      rw [hlen']
      field_simp
    rw [hw]
    have hdenom :
        R / (3 * (((3 * Lambda : ℕ) : ℝ))) =
          (R / (3 * (Lambda : ℝ))) / 3 := by
      push_cast
      ring
    rw [← hdenom]
    exact hstrongtail
  have hrparent : (r : ℝ) ∈ Icc s.left s.right :=
    ⟨by linarith [hrleft, s.nondegenerate],
      by linarith [hrright, s.nondegenerate]⟩
  have hsource (x : ℝ) (hx : x ∈ Icc a b) :
      0 < |x - (r : ℝ)| ∧
        |x - (r : ℝ)| < (((r.den : ℕ) : ℝ) ^ (n + 3))⁻¹ := by
    have hxavoid := havoid x hx
    exact ⟨hxavoid.2.1, lt_of_lt_of_le hxavoid.2.2
      (fusionRadius_le_source_accuracy Q r.den (n + 3) r.den_pos hdenhi.le)⟩
  have htarget (x : ℝ) (hx : x ∈ Icc a b) :
      ∀ z : ℤ, ∀ k : ℕ, s.cutoff ≤ k → k < nextCutoff Q (n + 3) →
        ((k : ℝ) ^ 100)⁻¹ < |f x - (z : ℝ) / (k : ℝ)| := by
    intro z k hklo hkhi
    have hxparent : x ∈ Icc s.left s.right :=
      ⟨(habsub hx).1.le, (habsub hx).2.le⟩
    have hclose : |x - (r : ℝ)| ≤ ((Q : ℝ) ^ (n + 3))⁻¹ :=
      le_trans (havoid x hx).2.2.le
        (fusionRadius_le_source_accuracy Q Q (n + 3) (by omega) (by omega))
    have hkT : (k : ℝ) < targetCutoff Q (n + 3) :=
      lt_of_lt_of_le (by exact_mod_cast hkhi)
        (nextCutoff_le_targetCutoff Q (n + 3))
    have hcut : 2 ≤ s.cutoff := s.cutoff_ge_two
    have hkpos : 0 < k := by omega
    exact safeCenter_avoidance_of_deriv_bound f s.left s.right d.M Q (n + 3)
      s.cutoff r x d.M_nonneg hsafe
      (fun y hy => d.differentiable y (hparent hy))
      (fun y hy => d.deriv_bound y (hparent hy))
      hrparent hxparent hclose z k hkpos hklo hkT
  let leftStage : FusionStage d (n + 1) := {
    left := a
    right := a + w
    nondegenerate := hleftpos
    contained := by
      intro x hx
      exact s.contained
        ⟨(habsub (hleftsub hx)).1.le, (habsub (hleftsub hx)).2.le⟩
    avoids := by
      intro x hx
      exact (havoid x (hleftsub hx)).1
    cutoff := nextCutoff Q (n + 3)
    cutoff_ge_two := hnext_two
    tail := by
      simpa [hleftlen] using hchildtail
    previousDen := r.den
  }
  let rightStage : FusionStage d (n + 1) := {
    left := a + 2 * w
    right := b
    nondegenerate := hrightpos
    contained := by
      intro x hx
      exact s.contained
        ⟨(habsub (hrightsub hx)).1.le, (habsub (hrightsub hx)).2.le⟩
    avoids := by
      intro x hx
      exact (havoid x (hrightsub hx)).1
    cutoff := nextCutoff Q (n + 3)
    cutoff_ge_two := hnext_two
    tail := by
      rw [hrightlen]
      exact hchildtail
    previousDen := r.den
  }
  refine ⟨{
    height := Q
    height_ge_two := hQ
    height_growth := by omega
    center := r
    den_lower := hdenlo
    den_upper := hdenhi
    leftChild := leftStage
    rightChild := rightStage
    left_nested := ?_
    right_nested := ?_
    separated := ?_
    left_cutoff := rfl
    right_cutoff := rfl
    cutoff_growth_left := hnext
    cutoff_growth_right := hnext
    left_previousDen := rfl
    right_previousDen := rfl
    source_left := ?_
    source_right := ?_
    target_left := ?_
    target_right := ?_ }⟩
  · intro x hx
    exact habsub (hleftsub hx)
  · intro x hx
    exact habsub (hrightsub hx)
  · exact hsep
  · intro x hx
    exact hsource x (hleftsub hx)
  · intro x hx
    exact hsource x (hrightsub hx)
  · intro x hx z k hklo hkhi
    exact htarget x (hleftsub hx) z k hklo (by simpa [leftStage] using hkhi)
  · intro x hx z k hklo hkhi
    exact htarget x (hrightsub hx) z k hklo (by simpa [rightStage] using hkhi)

end MahlerLean
