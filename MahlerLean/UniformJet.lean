import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic
import MahlerLean.WronskianLocalization

/-!
Uniform lower bounds for jets under Wronskian nondegeneracy.

This is the compactness core of Lemma 3.5 in the manuscript.  Instead of
introducing the least singular value explicitly, we use the equivalent
continuous positive function
  (c,x) ↦ ∑ k, |∑ j, φ_j^(k)(x) c_j|
on the compact product of the coefficient unit sphere and the source
compact set.
-/

noncomputable section
namespace MahlerLean

open Set Metric

/-- The jet matrix whose determinant is the Wronskian. -/
def jetMatrix {N : ℕ} (φ : Fin N → ℝ → ℝ) (x : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun k j => iteratedDeriv k.val (φ j) x

@[simp]
theorem jetMatrix_det {N : ℕ} (φ : Fin N → ℝ → ℝ) (x : ℝ) :
    (jetMatrix φ x).det = wronskian φ x := rfl

/-- The kth derivative-coordinate of the linear combination with coefficient vector c. -/
def jetApply {N : ℕ} (φ : Fin N → ℝ → ℝ)
    (c : EuclideanSpace ℝ (Fin N)) (k : Fin N) (x : ℝ) : ℝ :=
  ∑ j, iteratedDeriv k.val (φ j) x * c j

/-- The L1 norm of the first N jet coordinates of a normalized combination. -/
def jetL1 {N : ℕ} (φ : Fin N → ℝ → ℝ)
    (c : EuclideanSpace ℝ (Fin N)) (x : ℝ) : ℝ :=
  ∑ k, |jetApply φ c k x|

theorem jetApply_eq_mulVec {N : ℕ} (φ : Fin N → ℝ → ℝ)
    (c : EuclideanSpace ℝ (Fin N)) (x : ℝ) (k : Fin N) :
    jetApply φ c k x = (jetMatrix φ x).mulVec (fun j => c j) k := by
  simp [jetApply, jetMatrix, Matrix.mulVec, dotProduct]

theorem jetL1_nonneg {N : ℕ} (φ : Fin N → ℝ → ℝ)
    (c : EuclideanSpace ℝ (Fin N)) (x : ℝ) :
    0 ≤ jetL1 φ c x := by
  unfold jetL1
  positivity

/-- Joint continuity of one jet coordinate on coefficient-space times the source compact set. -/
theorem jetApply_continuousOn {N : ℕ} (φ : Fin N → ℝ → ℝ) {K : Set ℝ}
    (hφ : ∀ k j : Fin N, ContinuousOn (iteratedDeriv k.val (φ j)) K)
    (k : Fin N) :
    ContinuousOn (fun p : EuclideanSpace ℝ (Fin N) × ℝ => jetApply φ p.1 k p.2)
      (Set.univ ×ˢ K) := by
  unfold jetApply
  apply Finset.continuousOn_sum
  intro j hj
  have hc : Continuous (fun p : EuclideanSpace ℝ (Fin N) × ℝ => p.1 j) := by
    fun_prop
  have hd : ContinuousOn
      (fun p : EuclideanSpace ℝ (Fin N) × ℝ => iteratedDeriv k.val (φ j) p.2)
      (Set.univ ×ˢ K) := by
    exact (hφ k j).comp continuous_snd.continuousOn (by
      intro p hp
      exact hp.2)
  exact hd.mul hc.continuousOn

/-- Joint continuity of the L1 jet size. -/
theorem jetL1_continuousOn {N : ℕ} (φ : Fin N → ℝ → ℝ) {K : Set ℝ}
    (hφ : ∀ k j : Fin N, ContinuousOn (iteratedDeriv k.val (φ j)) K) :
    ContinuousOn (fun p : EuclideanSpace ℝ (Fin N) × ℝ => jetL1 φ p.1 p.2)
      (Set.univ ×ˢ K) := by
  unfold jetL1
  apply Finset.continuousOn_sum
  intro k hk
  exact (jetApply_continuousOn φ hφ k).abs

/-- If the Wronskian is nonzero and c is a unit vector, then its N-jet is nonzero. -/
theorem jetL1_pos_of_wronskian_ne_zero {N : ℕ} (hN : 0 < N)
    (φ : Fin N → ℝ → ℝ) (c : EuclideanSpace ℝ (Fin N)) (x : ℝ)
    (hc : ‖c‖ = 1) (hW : wronskian φ x ≠ 0) :
    0 < jetL1 φ c x := by
  have hc0 : c ≠ 0 := by
    intro hz
    simp [hz] at hc
  have hinj : Function.Injective (jetMatrix φ x).mulVec := by
    rw [Matrix.mulVec_injective_iff]
    exact Matrix.linearIndependent_cols_of_det_ne_zero (by simpa using hW)
  have hvne : (jetMatrix φ x).mulVec (fun j => c j) ≠ 0 := by
    intro hz
    have hfun : (fun j => c j) = 0 := hinj (by simpa using hz)
    apply hc0
    ext j
    exact congrFun hfun j
  apply lt_of_le_of_ne (jetL1_nonneg φ c x)
  intro hz
  apply hvne
  funext k
  rw [← jetApply_eq_mulVec]
  have hall :
      ∀ i ∈ (Finset.univ : Finset (Fin N)), |jetApply φ c i x| = 0 := by
    apply (Finset.sum_eq_zero_iff_of_nonneg (fun i hi => abs_nonneg _)).mp
    simpa [jetL1] using hz.symm
  exact abs_eq_zero.mp (hall k (by simp))

/-- Compactness upgrades pointwise jet nonvanishing to a uniform positive lower bound. -/
theorem exists_uniform_jetL1_lower_bound {N : ℕ} (hN : 0 < N)
    (φ : Fin N → ℝ → ℝ) {K : Set ℝ}
    (hK : IsCompact K)
    (hφ : ∀ k j : Fin N, ContinuousOn (iteratedDeriv k.val (φ j)) K)
    (hW : ∀ x ∈ K, wronskian φ x ≠ 0) :
    ∃ η : ℝ, 0 < η ∧
      ∀ c : EuclideanSpace ℝ (Fin N), ‖c‖ = 1 →
      ∀ x ∈ K, η ≤ jetL1 φ c x := by
  by_cases hKne : K.Nonempty
  · let S : Set (EuclideanSpace ℝ (Fin N)) := Metric.sphere 0 1
    let P : Set (EuclideanSpace ℝ (Fin N) × ℝ) := S ×ˢ K
    have hS : IsCompact S := by
      exact isCompact_sphere 0 1
    have hP : IsCompact P := hS.prod hK
    let i0 : Fin N := ⟨0, hN⟩
    let c0 : EuclideanSpace ℝ (Fin N) := EuclideanSpace.single i0 1
    have hc0 : ‖c0‖ = 1 := by simp [c0]
    have hc0S : c0 ∈ S := by
      simpa [S, Metric.mem_sphere] using hc0
    obtain ⟨x0, hx0⟩ := hKne
    have hPne : P.Nonempty := ⟨(c0, x0), hc0S, hx0⟩
    have hcont : ContinuousOn
        (fun p : EuclideanSpace ℝ (Fin N) × ℝ => jetL1 φ p.1 p.2) P := by
      exact (jetL1_continuousOn φ hφ).mono (by
        intro p hp
        exact ⟨Set.mem_univ p.1, hp.2⟩)
    obtain ⟨p, hp, hmin⟩ := hP.exists_isMinOn hPne hcont
    have hpunit : ‖p.1‖ = 1 := by
      simpa [P, S, Metric.mem_sphere] using hp.1
    have hpos : 0 < jetL1 φ p.1 p.2 :=
      jetL1_pos_of_wronskian_ne_zero hN φ p.1 p.2 hpunit (hW p.2 hp.2)
    refine ⟨jetL1 φ p.1 p.2, hpos, ?_⟩
    intro c hc x hx
    apply hmin
    refine ⟨?_, hx⟩
    simpa [S, Metric.mem_sphere] using hc
  · refine ⟨1, zero_lt_one, ?_⟩
    intro c hc x hx
    exact (hKne ⟨x, hx⟩).elim

/-- Analytic families satisfy the continuity hypothesis automatically. -/
theorem exists_uniform_jetL1_lower_bound_of_analytic {N : ℕ} (hN : 0 < N)
    (φ : Fin N → ℝ → ℝ) {U K : Set ℝ}
    (hφ : ∀ j, AnalyticOnNhd ℝ (φ j) U)
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hW : ∀ x ∈ K, wronskian φ x ≠ 0) :
    ∃ η : ℝ, 0 < η ∧
      ∀ c : EuclideanSpace ℝ (Fin N), ‖c‖ = 1 →
      ∀ x ∈ K, η ≤ jetL1 φ c x := by
  apply exists_uniform_jetL1_lower_bound hN φ hK
  · intro k j
    have ha : AnalyticOnNhd ℝ (iteratedDeriv k.val (φ j)) U := by
      rw [iteratedDeriv_eq_iterate]
      exact (hφ j).iterated_deriv k.val
    exact ha.continuousOn.mono hKU
  · exact hW

/-- Specialization to the manuscript's rational family x^i f(x)^j. -/
theorem exists_rationalFamily_uniform_jetL1_lower_bound
    {f : ℝ → ℝ} {U K : Set ℝ} (hf : AnalyticOnNhd ℝ f U)
    (d : ℕ) (hK : IsCompact K) (hKU : K ⊆ U)
    (hW : ∀ x ∈ K, rationalWronskian f d x ≠ 0) :
    ∃ η : ℝ, 0 < η ∧
      ∀ c : EuclideanSpace ℝ (Fin (2 * (d + 1))), ‖c‖ = 1 →
      ∀ x ∈ K, η ≤ jetL1 (rationalFamily f d) c x := by
  apply exists_uniform_jetL1_lower_bound_of_analytic (N := 2 * (d + 1)) (by omega)
    (rationalFamily f d) (fun j => rationalFamily_analytic hf d j) hK hKU
  simpa [rationalWronskian] using hW

end MahlerLean
