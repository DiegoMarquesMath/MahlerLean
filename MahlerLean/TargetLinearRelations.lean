import MahlerLean.DeterminantRelations
import MahlerLean.DeterminantAnalyticBounds

/-!
Common normalized relations for target-linear evaluation rows, together with
the transfer from exact rational target values to an approximate analytic
graph.
-/

open scoped BigOperators

noncomputable section
namespace MahlerLean

/-- Vanishing of every maximal target-linear determinant gives one unit
coefficient vector annihilating every evaluation row in the finite family. -/
theorem exists_unit_targetLinear_relation_of_all_det_zero
    (d : ℕ) {ι : Type*} [Fintype ι] (x y : ι → ℝ)
    (hdet : ∀ rows : Fin (2 * (d + 1)) → ι,
      (targetLinearMatrix d (x ∘ rows) (y ∘ rows)).det = 0) :
    ∃ c : EuclideanSpace ℝ (Fin (2 * (d + 1))), ‖c‖ = 1 ∧
      ∀ i, ∑ j, c j * (x i ^ (j.val / 2) * y i ^ (j.val % 2)) = 0 := by
  let v : ι → EuclideanSpace ℝ (Fin (2 * (d + 1))) := fun i ↦
    WithLp.toLp 2 (fun j ↦ x i ^ (j.val / 2) * y i ^ (j.val % 2))
  obtain ⟨c, hc, hrel⟩ := exists_unit_relation_of_all_det_zero v (by
    intro rows
    simpa only [targetLinearMatrix, Function.comp_apply, v, PiLp.toLp_apply] using hdet rows)
  refine ⟨c, hc, ?_⟩
  intro i
  simpa only [v, PiLp.toLp_apply] using hrel i

/-- A unit relation at an approximate target value becomes a controlled
sublevel relation on the graph.  The loss is linear in the vertical error and
keeps the source degree `d` explicit. -/
theorem norm_targetLinear_graph_relation_le_of_approx
    (d : ℕ) {c : EuclideanSpace ℝ (Fin (2 * (d + 1)))}
    (hc : ‖c‖ = 1) {x y z X δ : ℝ}
    (hX : 1 ≤ X) (hx : |x| ≤ X) (hδ : |y - z| ≤ δ)
    (hrel : ∑ j, c j * (x ^ (j.val / 2) * y ^ (j.val % 2)) = 0) :
    ‖∑ j, c j * (x ^ (j.val / 2) * z ^ (j.val % 2))‖ ≤
      (2 * (d + 1) : ℕ) * (X ^ d * δ) := by
  have hcj (j : Fin (2 * (d + 1))) : |c j| ≤ 1 := by
    have := PiLp.norm_apply_le c j
    simpa only [Real.norm_eq_abs, hc] using this
  have hpert :
      |∑ j, c j * targetLinearPerturbation d x y z j| ≤
        (2 * (d + 1) : ℕ) * (X ^ d * δ) := by
    calc
      |∑ j, c j * targetLinearPerturbation d x y z j| ≤
          ∑ j, |c j * targetLinearPerturbation d x y z j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, |targetLinearPerturbation d x y z j| := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (hcj j)
            (abs_nonneg (targetLinearPerturbation d x y z j))
      _ ≤ _ := targetLinearPerturbation_l1_le d hX hx hδ
  have hdecomp :
      (∑ j, c j * (x ^ (j.val / 2) * y ^ (j.val % 2))) =
        (∑ j, c j * (x ^ (j.val / 2) * z ^ (j.val % 2))) +
          ∑ j, c j * targetLinearPerturbation d x y z j := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    simp only [targetLinearPerturbation]
    ring
  have hgraph :
      (∑ j, c j * (x ^ (j.val / 2) * z ^ (j.val % 2))) =
        -∑ j, c j * targetLinearPerturbation d x y z j := by
    linarith
  rw [Real.norm_eq_abs, hgraph, abs_neg]
  exact hpert

/-- Combined rank-and-transfer bridge for a finite family of approximate graph
points. -/
theorem exists_unit_targetLinear_graph_sublevel_of_all_det_zero
    (d : ℕ) {ι : Type*} [Fintype ι]
    (x y : ι → ℝ) {f : ℝ → ℝ} {X δ : ℝ}
    (hdet : ∀ rows : Fin (2 * (d + 1)) → ι,
      (targetLinearMatrix d (x ∘ rows) (y ∘ rows)).det = 0)
    (hX : 1 ≤ X) (hx : ∀ i, |x i| ≤ X)
    (happrox : ∀ i, |y i - f (x i)| ≤ δ) :
    ∃ c : EuclideanSpace ℝ (Fin (2 * (d + 1))), ‖c‖ = 1 ∧
      ∀ i, ‖∑ j, c j *
        (x i ^ (j.val / 2) * f (x i) ^ (j.val % 2))‖ ≤
          (2 * (d + 1) : ℕ) * (X ^ d * δ) := by
  obtain ⟨c, hc, hrel⟩ :=
    exists_unit_targetLinear_relation_of_all_det_zero d x y hdet
  refine ⟨c, hc, ?_⟩
  intro i
  exact norm_targetLinear_graph_relation_le_of_approx d hc hX (hx i)
    (happrox i) (hrel i)

end MahlerLean
