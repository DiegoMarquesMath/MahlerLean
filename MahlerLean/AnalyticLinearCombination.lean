import MahlerLean.UniformJet

/-!
Analytic linear combinations and their jet coordinates.

This module is the first bridge in Step 12.  It identifies the iterated
derivatives of a normalized analytic linear combination with the jet
coordinates from `UniformJet`, and supplies the regularity hypotheses used
by `SublevelOneDim`.  It does not yet assert the full uniform sublevel lemma.
-/

open Set
open MeasureTheory
open scoped Topology Interval

noncomputable section
namespace MahlerLean

/-- Linear combination associated with a coefficient vector. -/
def jetLinearCombo {N : ℕ}
    (φ : Fin N → ℝ → ℝ)
    (c : EuclideanSpace ℝ (Fin N)) :
    ℝ → ℝ :=
  fun x => ∑ j, c j * φ j x

/-- Analyticity of a finite linear combination. -/
theorem analyticOnNhd_jetLinearCombo
    {N : ℕ}
    (φ : Fin N → ℝ → ℝ)
    (c : EuclideanSpace ℝ (Fin N))
    {U : Set ℝ}
    (hφ : ∀ j, AnalyticOnNhd ℝ (φ j) U) :
    AnalyticOnNhd ℝ (jetLinearCombo φ c) U := by
  unfold jetLinearCombo
  simpa using
    (Finset.univ : Finset (Fin N)).analyticOnNhd_fun_sum
      (fun j _ =>
        (analyticOnNhd_const (𝕜 := ℝ) (s := U) (v := c j)).mul
          (hφ j))

/-- The kth derivative of the linear combination equals the kth jet
coordinate used in Step 10. -/
theorem iteratedDeriv_jetLinearCombo_eq_jetApply
    {N : ℕ}
    (φ : Fin N → ℝ → ℝ)
    (c : EuclideanSpace ℝ (Fin N))
    {U : Set ℝ}
    (hφ : ∀ j, AnalyticOnNhd ℝ (φ j) U)
    {x : ℝ} (hx : x ∈ U)
    (k : Fin N) :
    iteratedDeriv k.val (jetLinearCombo φ c) x =
      jetApply φ c k x := by
  classical

  have hsum :
      ∀ s : Finset (Fin N),
        iteratedDeriv k.val
            (fun y => ∑ j ∈ s, c j * φ j y) x
          =
        ∑ j ∈ s,
          c j * iteratedDeriv k.val (φ j) x := by
    intro s
    induction s using Finset.induction_on with

    | empty =>
        have hkSmooth :
            ContDiffAt ℝ k.val (φ k) x :=
          (hφ k x hx).contDiffAt (n := k.val)

        have hz :=
          iteratedDeriv_const_mul
            (x := x) hkSmooth (0 : ℝ)

        simpa using hz

    | @insert j s hj ih =>
        have hjSmooth :
            ContDiffAt ℝ k.val (φ j) x :=
          (hφ j x hx).contDiffAt (n := k.val)

        have hsSmooth :
            ContDiffAt ℝ k.val
              (fun y => ∑ i ∈ s, c i * φ i y) x := by
          refine ContDiffAt.sum
            (s := s)
            (f := fun i y => c i * φ i y) ?_
          intro i hi
          exact
            contDiffAt_const.mul
              ((hφ i x hx).contDiffAt (n := k.val))

        have hadd :
            iteratedDeriv k.val
                (fun y =>
                  c j * φ j y +
                    ∑ i ∈ s, c i * φ i y) x
              =
            iteratedDeriv k.val
                (fun y => c j * φ j y) x
              +
            iteratedDeriv k.val
                (fun y => ∑ i ∈ s, c i * φ i y) x := by
          simpa only [Pi.add_apply] using
            (iteratedDeriv_add
              (f := fun y => c j * φ j y)
              (g := fun y => ∑ i ∈ s, c i * φ i y)
              (contDiffAt_const.mul hjSmooth)
              hsSmooth)

        calc
          iteratedDeriv k.val
              (fun y =>
                ∑ i ∈ insert j s, c i * φ i y) x
              =
            iteratedDeriv k.val
              (fun y =>
                c j * φ j y +
                  ∑ i ∈ s, c i * φ i y) x := by
                apply congrArg
                  (fun F : ℝ → ℝ =>
                    iteratedDeriv k.val F x)
                funext y
                rw [Finset.sum_insert hj]

          _ =
            iteratedDeriv k.val
                (fun y => c j * φ j y) x
              +
            iteratedDeriv k.val
                (fun y => ∑ i ∈ s, c i * φ i y) x :=
              hadd

          _ =
            c j * iteratedDeriv k.val (φ j) x
              +
            ∑ i ∈ s,
              c i * iteratedDeriv k.val (φ i) x := by
                rw [iteratedDeriv_const_mul hjSmooth (c j)]
                rw [ih]

          _ =
            ∑ i ∈ insert j s,
              c i * iteratedDeriv k.val (φ i) x := by
                rw [Finset.sum_insert hj]

  unfold jetLinearCombo jetApply

  have h := hsum (Finset.univ : Finset (Fin N))
  simpa [mul_comm] using h

/-- Analyticity supplies all regularity assumptions required by Step 11. -/
theorem analyticFamily_linearCombo_smooth
    {N : ℕ}
    (φ : Fin N → ℝ → ℝ)
    (c : EuclideanSpace ℝ (Fin N))
    {U : Set ℝ}
    (hφ : ∀ j, AnalyticOnNhd ℝ (φ j) U)
    {a b : ℝ}
    (hI : Icc a b ⊆ U) :
    (∀ r : ℕ,
        ContinuousOn
          (iteratedDeriv r (jetLinearCombo φ c))
          (Icc a b))
      ∧
    (∀ r : ℕ, ∀ x ∈ Icc a b,
        DifferentiableAt ℝ
          (iteratedDeriv r (jetLinearCombo φ c)) x) := by

  have hlin :
      AnalyticOnNhd ℝ (jetLinearCombo φ c) U :=
    analyticOnNhd_jetLinearCombo φ c hφ

  constructor

  · intro r

    have hr :
        AnalyticOnNhd ℝ
          (iteratedDeriv r (jetLinearCombo φ c)) U := by
      rw [iteratedDeriv_eq_iterate]
      exact hlin.iterated_deriv r

    exact hr.continuousOn.mono hI

  · intro r x hx

    have hr :
        AnalyticAt ℝ
          (iteratedDeriv r (jetLinearCombo φ c)) x := by
      rw [iteratedDeriv_eq_iterate]
      exact (hlin x (hI hx)).iterated_deriv r

    exact hr.differentiableAt

end MahlerLean
