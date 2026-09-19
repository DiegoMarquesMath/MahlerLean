import MahlerLean.AnalyticLinearCombination

/-!
Local persistence of the jet lower bound.

This is the second bridge in Step 12.  A jet coordinate which is large at
one point remains large nearby.  The product-space version is relative to
the compact set on which the Wronskian is assumed nonzero; this is the form
needed for the later finite-subcover argument.
-/

open Set
open scoped Topology

noncomputable section
namespace MahlerLean

/-- A lower bound for one jet coordinate at `x` persists as a lower bound
for the corresponding derivative of the scalar linear combination on a
neighborhood of `x`. -/
theorem exists_nhds_iteratedDeriv_abs_lower_bound
    {N : ℕ}
    (φ : Fin N → ℝ → ℝ)
    (c : EuclideanSpace ℝ (Fin N))
    {U : Set ℝ}
    (hφ : ∀ j, AnalyticOnNhd ℝ (φ j) U)
    {x η : ℝ}
    (hx : x ∈ U)
    (k : Fin N)
    (hη : 0 < η)
    (hlow : η ≤ |jetApply φ c k x|) :
    ∃ V : Set ℝ,
      V ∈ 𝓝 x ∧
      ∀ y ∈ V,
        η / 2 ≤
          |iteratedDeriv k.val (jetLinearCombo φ c) y| := by

  have hlin :
      AnalyticAt ℝ (jetLinearCombo φ c) x :=
    (analyticOnNhd_jetLinearCombo φ c hφ) x hx

  have hkAnalytic :
      AnalyticAt ℝ
        (iteratedDeriv k.val (jetLinearCombo φ c)) x := by
    rw [iteratedDeriv_eq_iterate]
    exact hlin.iterated_deriv k.val

  have hcont :
      ContinuousAt
        (fun y =>
          |iteratedDeriv k.val (jetLinearCombo φ c) y|) x :=
    hkAnalytic.continuousAt.abs

  have hcenter :
      η ≤ |iteratedDeriv k.val (jetLinearCombo φ c) x| := by
    rw [iteratedDeriv_jetLinearCombo_eq_jetApply φ c hφ hx k]
    exact hlow

  have hstrict :
      η / 2 <
        |iteratedDeriv k.val (jetLinearCombo φ c) x| := by
    linarith

  let V : Set ℝ :=
    {y |
      η / 2 <
        |iteratedDeriv k.val (jetLinearCombo φ c) y|}

  have hV : V ∈ 𝓝 x := by
    simpa [V] using hcont (Ioi_mem_nhds hstrict)

  refine ⟨V, hV, ?_⟩
  intro y hy
  exact le_of_lt (by simpa [V] using hy)

/-- Relative product-neighborhood version of persistence.  The coefficient
vector and the source point are both allowed to vary. -/
theorem exists_product_nhds_jetApply_abs_lower_bound
    {N : ℕ}
    (φ : Fin N → ℝ → ℝ)
    {K : Set ℝ}
    (hφ :
      ∀ k j : Fin N,
        ContinuousOn (iteratedDeriv k.val (φ j)) K)
    {c : EuclideanSpace ℝ (Fin N)}
    {x η : ℝ}
    (hx : x ∈ K)
    (k : Fin N)
    (hη : 0 < η)
    (hlow : η ≤ |jetApply φ c k x|) :
    ∃ V : Set (EuclideanSpace ℝ (Fin N) × ℝ),
      V ∈ 𝓝[Set.univ ×ˢ K] (c, x) ∧
      ∀ p ∈ V,
        η / 2 ≤ |jetApply φ p.1 k p.2| := by

  have hcont :
      ContinuousWithinAt
        (fun p : EuclideanSpace ℝ (Fin N) × ℝ =>
          |jetApply φ p.1 k p.2|)
        (Set.univ ×ˢ K) (c, x) :=
    ((jetApply_continuousOn φ hφ k)
      (c, x) ⟨Set.mem_univ c, hx⟩).abs

  have hstrict :
      η / 2 < |jetApply φ c k x| := by
    linarith

  let V : Set (EuclideanSpace ℝ (Fin N) × ℝ) :=
    {p | η / 2 < |jetApply φ p.1 k p.2|}

  have hV : V ∈ 𝓝[Set.univ ×ˢ K] (c, x) := by
    simpa [V] using hcont (Ioi_mem_nhds hstrict)

  refine ⟨V, hV, ?_⟩
  intro p hp
  exact le_of_lt (by simpa [V] using hp)

/-- Uniform analytic specialization: the same positive `η` works at every
unit coefficient vector and every point of `K`; only the coordinate and
the product neighborhood depend on the point. -/
theorem exists_uniform_product_nhds_jetApply_lower_bound_of_analytic
    {N : ℕ}
    (hN : 0 < N)
    (φ : Fin N → ℝ → ℝ)
    {U K : Set ℝ}
    (hφ : ∀ j, AnalyticOnNhd ℝ (φ j) U)
    (hK : IsCompact K)
    (hKU : K ⊆ U)
    (hW : ∀ x ∈ K, wronskian φ x ≠ 0) :
    ∃ η : ℝ,
      0 < η ∧
      ∀ c : EuclideanSpace ℝ (Fin N),
        ‖c‖ = 1 →
        ∀ x ∈ K,
          ∃ k : Fin N,
          ∃ V : Set (EuclideanSpace ℝ (Fin N) × ℝ),
            V ∈ 𝓝[Set.univ ×ˢ K] (c, x) ∧
            ∀ p ∈ V,
              η / 2 ≤ |jetApply φ p.1 k p.2| := by

  obtain ⟨η, hη, huniform⟩ :=
    exists_uniform_jet_coordinate_lower_bound_of_analytic
      hN φ hφ hK hKU hW

  have hderivCont :
      ∀ k j : Fin N,
        ContinuousOn (iteratedDeriv k.val (φ j)) K := by
    intro k j
    have ha :
        AnalyticOnNhd ℝ
          (iteratedDeriv k.val (φ j)) U := by
      rw [iteratedDeriv_eq_iterate]
      exact (hφ j).iterated_deriv k.val
    exact ha.continuousOn.mono hKU

  refine ⟨η, hη, ?_⟩
  intro c hc x hx
  obtain ⟨k, hk⟩ := huniform c hc x hx
  obtain ⟨V, hV, hbound⟩ :=
    exists_product_nhds_jetApply_abs_lower_bound
      φ hderivCont hx k hη hk
  exact ⟨k, V, hV, hbound⟩

end MahlerLean
