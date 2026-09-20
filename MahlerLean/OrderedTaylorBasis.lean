import MahlerLean.WronskianLeadingMatrix
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

noncomputable section
namespace MahlerLean
open Module
universe u

/-- A separating sequence of linear forms admits a basis with distinct first nonzero indices. -/
theorem exists_basis_distinct_orders (n : ℕ) :
    ∀ (V : Type u) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V],
    finrank ℝ V = n → ∀ L : ℕ → V →ₗ[ℝ] ℝ,
    (∀ v, (∀ k, L k v = 0) → v = 0) →
    ∃ b : Basis (Fin n) ℝ V, ∃ r : Fin n → ℕ,
      Function.Injective r ∧ ∀ i, L (r i) (b i) ≠ 0 ∧ ∀ k < r i, L k (b i) = 0 := by
  classical
  induction n with
  | zero =>
    intro V _ _ _ hdim L hsep
    let b : Basis (Fin 0) ℝ V := (Module.finBasis ℝ V).reindex (finCongr hdim)
    exact ⟨b, Fin.elim0, (fun i ↦ Fin.elim0 i), (fun i ↦ Fin.elim0 i)⟩
  | succ n ih =>
    intro V _ _ _ hdim L hsep
    haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (by omega : 0 < finrank ℝ V)
    have hex : ∃ k, ∃ v, L k v ≠ 0 := by
      obtain ⟨v, hv⟩ := exists_ne (0 : V)
      by_contra h
      push_neg at h
      exact hv (hsep v (fun k ↦ h k v))
    let k := Nat.find hex
    obtain ⟨v, hv⟩ := Nat.find_spec hex
    have hmin : ∀ j < k, ∀ w, L j w = 0 := by
      intro j hj w
      exact not_not.mp (fun hn ↦ Nat.find_min hex hj ⟨w, hn⟩)
    let K := LinearMap.ker (L k)
    have hsur : Function.Surjective (L k) := by
      intro t
      refine ⟨(t / L k v) • v, ?_⟩
      simp only [map_smul, smul_eq_mul]
      exact div_mul_cancel₀ t hv
    have hdimK : finrank ℝ K = n := by
      have h := (L k).finrank_range_add_finrank_ker
      rw [LinearMap.range_eq_top.mpr hsur, finrank_top, finrank_self, hdim] at h
      dsimp [K]
      omega
    let LK : ℕ → K →ₗ[ℝ] ℝ := fun j ↦ (L j).comp K.subtype
    obtain ⟨b, r, hr, hb⟩ := ih K hdimK LK (by
      intro w hw
      apply Subtype.ext
      exact hsep w hw)
    have hli : ∀ c : ℝ, ∀ w ∈ K, c • v + w = 0 → c = 0 := by
      intro c w hw he
      have he' := congrArg (L k) he
      have hw' : L k w = 0 := hw
      simp only [map_add, map_smul, map_zero, smul_eq_mul, hw', add_zero] at he'
      exact (mul_eq_zero.mp he').resolve_right hv
    have hsp : ∀ w : V, ∃ c : ℝ, w + c • v ∈ K := by
      intro w
      refine ⟨-(L k w / L k v), ?_⟩
      change L k (w + -(L k w / L k v) • v) = 0
      simp only [map_add, map_smul, smul_eq_mul, neg_mul]
      rw [div_mul_cancel₀ _ hv, add_neg_cancel]
    let B := b.mkFinCons v hli hsp
    have hrne : ∀ i, r i ≠ k := by
      intro i he
      have h := (hb i).1
      rw [he] at h
      exact h (b i).property
    refine ⟨B, Fin.cons k r, ?_, ?_⟩
    · intro i j he
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => rfl
        | succ j => exact (hrne j (by simpa using he.symm)).elim
      | succ i =>
        cases j using Fin.cases with
        | zero => exact (hrne i (by simpa using he)).elim
        | succ j => exact congrArg Fin.succ (hr (by simpa using he))
    · intro i
      cases i using Fin.cases with
      | zero => simpa [B, Basis.coe_mkFinCons] using And.intro hv (fun j hj ↦ hmin j hj v)
      | succ i => simpa [B, Basis.coe_mkFinCons, LK] using hb i

end MahlerLean
