import MahlerLean.TargetLinearRelations
import MahlerLean.UniformSublevelDisjoint

/-!
The determinant-to-sublevel interface used by the counting argument.  It
packages the common normalized relation extracted from vanishing maximal
minors with the uniform analytic sublevel theorem.
-/

open Set MeasureTheory
open scoped BigOperators

noncomputable section
namespace MahlerLean

/-- A finite family of approximate graph points whose maximal target-linear
determinants all vanish lies in one controlled rational-relation sublevel set.
The measure and interval-complexity constants are independent of the finite
family and of its normalized relation. -/
theorem exists_uniform_sublevel_data_of_targetLinear_det_zero
    {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hf : AnalyticOnNhd ℝ f U) (d : ℕ)
    {A B : ℝ} (hAB : A ≤ B) (hJU : Icc A B ⊆ U)
    (hW : ∀ z ∈ Icc A B, rationalWronskian f d z ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∃ R : ℕ, 0 < R ∧
    ∃ eps0 : ℝ, 0 < eps0 ∧ eps0 < 1 ∧
      ∀ {ι : Type*} [Fintype ι]
        (x y : ι → ℝ) {X δ : ℝ},
        (∀ rows : Fin (2 * (d + 1)) → ι,
          (targetLinearMatrix d (x ∘ rows) (y ∘ rows)).det = 0) →
        1 ≤ X → (∀ i, |x i| ≤ X) →
        (∀ i, x i ∈ Icc A B) →
        0 ≤ δ → (∀ i, |y i - f (x i)| ≤ δ) →
        (2 * (d + 1) : ℕ) * (X ^ d * δ) < eps0 →
        ∃ c : EuclideanSpace ℝ (Fin (2 * (d + 1))),
          ‖c‖ = 1 ∧
          (∀ i, x i ∈ Icc A B ∧
            ‖∑ j, c j *
              (x i ^ (j.val / 2) * f (x i) ^ (j.val % 2))‖ ≤
                (2 * (d + 1) : ℕ) * (X ^ d * δ)) ∧
          (∃ t : Finset (Set ℝ), t.card ≤ R ∧
            (∀ E ∈ t, E.OrdConnected) ∧
            (t : Set (Set ℝ)).PairwiseDisjoint id ∧
            (∀ z, (z ∈ Icc A B ∧
              ‖∑ j, c j *
                (z ^ (j.val / 2) * f z ^ (j.val % 2))‖ ≤
                  (2 * (d + 1) : ℕ) * (X ^ d * δ)) ↔
                ∃ E ∈ t, z ∈ E)) ∧
          volume.real {z | z ∈ Icc A B ∧
            ‖∑ j, c j *
              (z ^ (j.val / 2) * f z ^ (j.val % 2))‖ ≤
                (2 * (d + 1) : ℕ) * (X ^ d * δ)} ≤
            C * ((2 * (d + 1) : ℕ) * (X ^ d * δ)) ^
              (((2 * (d + 1) - 1 : ℕ) : ℝ)⁻¹) := by
  obtain ⟨C, hC, R, hR, eps0, heps0, heps1, hsub⟩ :=
    exists_uniform_rational_relation_disjoint_sublevel_bound
      hU hf d hAB hJU hW
  refine ⟨C, hC, R, hR, eps0, heps0, heps1, ?_⟩
  intro ι _ x y X δ hdet hX hx hxI hδ0 happrox hsmall
  obtain ⟨c, hc, hcsmall⟩ :=
    exists_unit_targetLinear_graph_sublevel_of_all_det_zero
      d x y hdet hX hx happrox
  obtain ⟨hcover, hmeasure⟩ := hsub c hc
    ((2 * (d + 1) : ℕ) * (X ^ d * δ)) (by positivity) hsmall
  refine ⟨c, hc, ?_, hcover, hmeasure⟩
  intro i
  exact ⟨hxI i, hcsmall i⟩

end MahlerLean
