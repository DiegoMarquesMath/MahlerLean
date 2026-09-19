import MahlerLean.LocalJetPersistence
import Mathlib.Topology.Compactness.Compact

/-!
Finite product covers for the uniform jet argument.

This module performs the compactness extraction required in Step 12.  It
upgrades pointwise persistence to finitely many product neighborhoods on
the coefficient unit sphere times the compact source set.  It still does
not assert the final uniform sublevel or component estimate.
-/

open Set Metric
open scoped Topology

noncomputable section
namespace MahlerLean

/-- Product of the coefficient unit sphere with the compact source set. -/
def coefficientSourceProduct (N : ℕ) (K : Set ℝ) :
    Set (EuclideanSpace ℝ (Fin N) × ℝ) :=
  Metric.sphere 0 1 ×ˢ K

@[simp]
theorem mem_coefficientSourceProduct
    {N : ℕ} {K : Set ℝ}
    (p : EuclideanSpace ℝ (Fin N) × ℝ) :
    p ∈ coefficientSourceProduct N K ↔
      ‖p.1‖ = 1 ∧ p.2 ∈ K := by
  simp [coefficientSourceProduct]

/-- Analyticity gives joint continuity of a jet coordinate when both the
coefficient vector and the source point vary. -/
theorem jetApply_continuousAt_of_analytic
    {N : ℕ}
    (φ : Fin N → ℝ → ℝ)
    {U : Set ℝ}
    (hφ : ∀ j, AnalyticOnNhd ℝ (φ j) U)
    {c : EuclideanSpace ℝ (Fin N)}
    {x : ℝ}
    (hx : x ∈ U)
    (k : Fin N) :
    ContinuousAt
      (fun p : EuclideanSpace ℝ (Fin N) × ℝ =>
        jetApply φ p.1 k p.2)
      (c, x) := by
  unfold jetApply
  apply tendsto_finset_sum Finset.univ
  intro j hj

  have hjAnalytic :
      AnalyticAt ℝ (iteratedDeriv k.val (φ j)) x := by
    rw [iteratedDeriv_eq_iterate]
    exact (hφ j x hx).iterated_deriv k.val

  have hd :
      ContinuousAt
        (fun p : EuclideanSpace ℝ (Fin N) × ℝ =>
          iteratedDeriv k.val (φ j) p.2)
        (c, x) := by
    have hsnd :
        ContinuousAt
          (fun p : EuclideanSpace ℝ (Fin N) × ℝ => p.2)
          (c, x) :=
      continuousAt_snd
    simpa only [Function.comp_apply] using
      hjAnalytic.continuousAt.comp hsnd

  have hc :
      ContinuousAt
        (fun p : EuclideanSpace ℝ (Fin N) × ℝ => p.1 j)
        (c, x) := by
    fun_prop

  exact hd.mul hc

/-- Analytic product persistence in an ambient neighborhood, rather than
only a neighborhood relative to the compact product. -/
theorem exists_product_nhds_jetApply_abs_lower_bound_of_analytic
    {N : ℕ}
    (φ : Fin N → ℝ → ℝ)
    {U : Set ℝ}
    (hφ : ∀ j, AnalyticOnNhd ℝ (φ j) U)
    {c : EuclideanSpace ℝ (Fin N)}
    {x η : ℝ}
    (hx : x ∈ U)
    (k : Fin N)
    (hη : 0 < η)
    (hlow : η ≤ |jetApply φ c k x|) :
    ∃ V : Set (EuclideanSpace ℝ (Fin N) × ℝ),
      V ∈ 𝓝 (c, x) ∧
      ∀ p ∈ V,
        η / 2 ≤ |jetApply φ p.1 k p.2| := by

  have hcont :
      ContinuousAt
        (fun p : EuclideanSpace ℝ (Fin N) × ℝ =>
          |jetApply φ p.1 k p.2|)
        (c, x) :=
    (jetApply_continuousAt_of_analytic φ hφ hx k).abs

  have hstrict :
      η / 2 < |jetApply φ c k x| := by
    linarith

  let V : Set (EuclideanSpace ℝ (Fin N) × ℝ) :=
    {p | η / 2 < |jetApply φ p.1 k p.2|}

  have hV : V ∈ 𝓝 (c, x) := by
    simpa [V] using hcont (Ioi_mem_nhds hstrict)

  refine ⟨V, hV, ?_⟩
  intro p hp
  exact le_of_lt (by simpa [V] using hp)

/-- A finite product cover carrying a fixed derivative order on each patch.
The lower-bound constant is uniform over the whole compact product. -/
theorem exists_finite_uniform_jet_product_cover_of_analytic
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
      ∃ k : coefficientSourceProduct N K → Fin N,
      ∃ V : coefficientSourceProduct N K →
          Set (EuclideanSpace ℝ (Fin N) × ℝ),
        (∀ p : coefficientSourceProduct N K,
          V p ∈ 𝓝 (p : EuclideanSpace ℝ (Fin N) × ℝ)) ∧
        (∀ p : coefficientSourceProduct N K,
          ∀ q ∈ V p,
            η / 2 ≤ |jetApply φ q.1 (k p) q.2|) ∧
        ∃ t : Finset (coefficientSourceProduct N K),
          ∀ q ∈ coefficientSourceProduct N K,
            ∃ p ∈ t,
              q ∈ V p := by

  obtain ⟨η, hη, huniform⟩ :=
    exists_uniform_jet_coordinate_lower_bound_of_analytic
      hN φ hφ hK hKU hW

  have hP :
      IsCompact (coefficientSourceProduct N K) := by
    exact (isCompact_sphere (0 : EuclideanSpace ℝ (Fin N)) 1).prod hK

  have hlocal :
      ∀ p : coefficientSourceProduct N K,
        ∃ k : Fin N,
        ∃ V : Set (EuclideanSpace ℝ (Fin N) × ℝ),
          V ∈ 𝓝 (p : EuclideanSpace ℝ (Fin N) × ℝ) ∧
          ∀ q ∈ V,
            η / 2 ≤ |jetApply φ q.1 k q.2| := by
    intro p

    have hpdata :
        ‖p.1.1‖ = 1 ∧ p.1.2 ∈ K :=
      (mem_coefficientSourceProduct (K := K) p.1).mp p.2

    obtain ⟨k, hk⟩ :=
      huniform p.1.1 hpdata.1 p.1.2 hpdata.2

    obtain ⟨V, hV, hbound⟩ :=
      exists_product_nhds_jetApply_abs_lower_bound_of_analytic
        φ hφ (hKU hpdata.2) k hη hk

    exact ⟨k, V, hV, hbound⟩

  choose k V hV hbound using hlocal

  obtain ⟨t, ht⟩ :=
    hP.elim_nhds_subcover'
      (fun p hp => V ⟨p, hp⟩)
      (fun p hp => hV ⟨p, hp⟩)

  refine ⟨η, hη, k, V, hV, hbound, t, ?_⟩
  intro q hq
  rcases Set.mem_iUnion₂.mp (ht hq) with ⟨p, hp, hqp⟩
  exact ⟨p, hp, hqp⟩

end MahlerLean
