import MahlerLean.FiniteJetCover
import Mathlib.Topology.Constructions.SumProd

/-!
Uniform interval patches extracted from the compact product cover.

This module performs the topological step between the finite
coefficient/source cover and the finite interval assembly.  Each product
neighborhood is shrunk to a coefficient neighborhood times a compact
source interval.  Compactness then selects finitely many such rectangles.
-/

open Set Metric
open scoped Topology

noncomputable section
namespace MahlerLean

/-- A neighborhood of a coefficient/source pair contains a product of a
coefficient neighborhood with a compact interval around the source
point.  If the source point lies in an open set `U`, the interval can
be chosen inside `U`. -/
theorem exists_product_nhds_Icc_subset
    {N : ℕ}
    {V : Set (EuclideanSpace ℝ (Fin N) × ℝ)}
    {U : Set ℝ}
    {c : EuclideanSpace ℝ (Fin N)}
    {x : ℝ}
    (hV : V ∈ 𝓝 (c, x))
    (hU : IsOpen U)
    (hx : x ∈ U) :
    ∃ A : Set (EuclideanSpace ℝ (Fin N)),
    ∃ a b : ℝ,
      A ∈ 𝓝 c ∧
      a < x ∧
      x < b ∧
      Icc a b ⊆ U ∧
      A ×ˢ Icc a b ⊆ V := by

  rcases mem_nhds_prod_iff.mp hV with
    ⟨A, hA, B, hB, hprod⟩

  have hBU : B ∩ U ∈ 𝓝 x :=
    inter_mem hB (hU.mem_nhds hx)

  rcases Metric.mem_nhds_iff.mp hBU with
    ⟨eps, heps, hepsSub⟩

  have hIball :
      Icc (x - eps / 2) (x + eps / 2)
        ⊆ Metric.ball x eps := by
    intro y hy
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hy.1, hy.2]

  refine
    ⟨A, x - eps / 2, x + eps / 2,
      hA, by linarith, by linarith, ?_, ?_⟩

  · intro y hy
    exact (hepsSub (hIball hy)).2

  · rintro ⟨d, y⟩ ⟨hd, hy⟩
    exact hprod ⟨hd, (hepsSub (hIball hy)).1⟩

/-- Finite rectangular cover of the coefficient unit sphere times the
compact source set.  Every rectangle carries a fixed jet order, a compact
source interval inside the analytic domain, and the same positive lower
bound. -/
theorem exists_finite_uniform_jet_interval_cover_of_analytic
    {N : ℕ}
    (hN : 0 < N)
    (φ : Fin N → ℝ → ℝ)
    {U K : Set ℝ}
    (hU : IsOpen U)
    (hφ : ∀ j, AnalyticOnNhd ℝ (φ j) U)
    (hK : IsCompact K)
    (hKU : K ⊆ U)
    (hW : ∀ x ∈ K, wronskian φ x ≠ 0) :
    ∃ eta : ℝ,
      0 < eta ∧
      ∃ k : coefficientSourceProduct N K → Fin N,
      ∃ A : coefficientSourceProduct N K →
          Set (EuclideanSpace ℝ (Fin N)),
      ∃ a b : coefficientSourceProduct N K → ℝ,
        (∀ p : coefficientSourceProduct N K,
          A p ∈ 𝓝 p.1.1) ∧
        (∀ p : coefficientSourceProduct N K,
          a p < p.1.2 ∧ p.1.2 < b p) ∧
        (∀ p : coefficientSourceProduct N K,
          Icc (a p) (b p) ⊆ U) ∧
        (∀ p : coefficientSourceProduct N K,
          ∀ c' ∈ A p,
          ∀ x' ∈ Icc (a p) (b p),
            eta / 2 ≤ |jetApply φ c' (k p) x'|) ∧
        ∃ t : Finset (coefficientSourceProduct N K),
          ∀ q ∈ coefficientSourceProduct N K,
            ∃ p ∈ t,
              q.1.1 ∈ A p ∧
              q.1.2 ∈ Ioo (a p) (b p) := by

  obtain ⟨eta, heta, k, V, hV, hbound, _t, _ht⟩ :=
    exists_finite_uniform_jet_product_cover_of_analytic
      hN φ hφ hK hKU hW

  have hrect :
      ∀ p : coefficientSourceProduct N K,
        ∃ A : Set (EuclideanSpace ℝ (Fin N)),
        ∃ a b : ℝ,
          A ∈ 𝓝 p.1.1 ∧
          a < p.1.2 ∧
          p.1.2 < b ∧
          Icc a b ⊆ U ∧
          A ×ˢ Icc a b ⊆ V p := by
    intro p

    have hpdata :
        ‖p.1.1‖ = 1 ∧ p.1.2 ∈ K :=
      (mem_coefficientSourceProduct (K := K) p.1).mp p.2

    exact
      exists_product_nhds_Icc_subset
        (hV p) hU (hKU hpdata.2)

  choose A a b hA ha hb hIU hsub using hrect

  have hbox :
      ∀ p : coefficientSourceProduct N K,
        A p ×ˢ Ioo (a p) (b p)
          ∈ 𝓝 (p.1 :
            EuclideanSpace ℝ (Fin N) × ℝ) := by
    intro p
    apply mem_nhds_prod_iff.mpr
    exact
      ⟨A p, hA p,
        Ioo (a p) (b p),
        Ioo_mem_nhds (ha p) (hb p),
        Set.Subset.rfl⟩

  have hP :
      IsCompact (coefficientSourceProduct N K) := by
    exact
      (isCompact_sphere
        (0 : EuclideanSpace ℝ (Fin N)) 1).prod hK

  obtain ⟨t, ht⟩ :=
    hP.elim_nhds_subcover'
      (fun p hp =>
        A ⟨p, hp⟩ ×ˢ
          Ioo (a ⟨p, hp⟩) (b ⟨p, hp⟩))
      (fun p hp => hbox ⟨p, hp⟩)

  refine
    ⟨eta, heta, k, A, a, b,
      hA, ?_, hIU, ?_, t, ?_⟩

  · intro p
    exact ⟨ha p, hb p⟩

  · intro p c' hc x' hx'
    apply hbound p (c', x')
    exact hsub p ⟨hc, hx'⟩

  · intro q hq
    rcases Set.mem_iUnion₂.mp (ht hq) with
      ⟨p, hp, hqp⟩
    exact ⟨p, hp, hqp.1, hqp.2⟩

end MahlerLean
