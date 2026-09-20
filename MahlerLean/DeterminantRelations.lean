import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
Linear-algebra bridge from vanishing maximal determinants to a single
normalized relation shared by every row.  This is the rank step needed after
the determinant method has forced every maximal minor to vanish.
-/

open scoped BigOperators ComplexConjugate InnerProductSpace

noncomputable section
namespace MahlerLean

/-- If every square matrix obtained by selecting `N` rows from a finite family
has zero determinant, then all rows satisfy one common unit linear relation.
Repeated selections are allowed; this formulation avoids any cardinality side
condition on the row index type. -/
theorem exists_unit_relation_of_all_det_zero
    {N : ℕ} {ι : Type*} [Fintype ι]
    (v : ι → EuclideanSpace ℝ (Fin N))
    (hdet : ∀ rows : Fin N → ι,
      Matrix.det (fun i j ↦ v (rows i) j) = 0) :
    ∃ c : EuclideanSpace ℝ (Fin N), ‖c‖ = 1 ∧
      ∀ i, ∑ j, c j * v i j = 0 := by
  let W : Submodule ℝ (EuclideanSpace ℝ (Fin N)) :=
    Submodule.span ℝ (Set.range v)
  have hW : W ≠ ⊤ := by
    intro hWtop
    obtain ⟨κ, a, ha, hspan, hli⟩ :=
      exists_linearIndependent' ℝ v
    letI : Finite κ := hli.finite
    letI : Fintype κ := Fintype.ofFinite κ
    have hcard : Fintype.card κ = N := by
      have hdim := linearIndependent_iff_card_eq_finrank_span.mp hli
      rw [Set.finrank, hspan, show Submodule.span ℝ (Set.range v) = W from rfl,
        hWtop, finrank_top,
        finrank_euclideanSpace_fin] at hdim
      exact hdim
    have hcard' : Fintype.card (Fin N) = Fintype.card κ := by simp [hcard]
    let e : Fin N ≃ κ := Fintype.equivOfCardEq hcard'
    let rows : Fin N → ι := fun i ↦ a (e i)
    let M : Matrix (Fin N) (Fin N) ℝ := fun i j ↦ v (rows i) j
    have hliE : LinearIndependent ℝ (fun i ↦ v (rows i)) := by
      simpa only [rows, Function.comp_apply] using hli.comp e e.injective
    have hliM : LinearIndependent ℝ M.row := by
      have hmapped := hliE.map'
        (EuclideanSpace.equiv (Fin N) ℝ).toLinearMap
        (LinearMap.ker_eq_bot.mpr (EuclideanSpace.equiv (Fin N) ℝ).injective)
      simpa only [M, Matrix.row_apply, rows] using hmapped
    have hunit : IsUnit M := Matrix.linearIndependent_rows_iff_isUnit.mp hliM
    have hdetM : M.det ≠ 0 :=
      (M.isUnit_iff_isUnit_det.mp hunit).ne_zero
    exact hdetM (hdet rows)
  have horth : Wᗮ ≠ ⊥ := by
    intro hbot
    exact hW (Submodule.orthogonal_eq_bot_iff.mp hbot)
  obtain ⟨u, huW, hu0⟩ := (Submodule.ne_bot_iff Wᗮ).mp horth
  let c : EuclideanSpace ℝ (Fin N) := (‖u‖⁻¹ : ℝ) • u
  have hunorm : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu0
  have hcunit : ‖c‖ = 1 := by
    simp [c, norm_smul, hunorm]
  refine ⟨c, hcunit, ?_⟩
  intro i
  have hvi : v i ∈ W := Submodule.subset_span (Set.mem_range_self i)
  have hinner : ⟪c, v i⟫_ℝ = 0 :=
    W.inner_left_of_mem_orthogonal hvi (Wᗮ.smul_mem (‖u‖⁻¹ : ℝ) huW)
  simpa only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    mul_comm] using hinner

end MahlerLean
