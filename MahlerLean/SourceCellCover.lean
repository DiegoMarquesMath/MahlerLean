import MahlerLean.CellCountingAssembly
import Mathlib.Algebra.Order.Floor.Ring

open Set
noncomputable section
namespace MahlerLean

/-- A uniform grid of at most (b-a)/rho+1 cells covers the closed interval,
including its right endpoint; every cell base is strictly below b. -/
theorem exists_source_cell_cover {a b ρ : ℝ} (hab : a < b) (hρ : 0 < ρ) :
    ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ (b - a) / ρ + 1 ∧
      ∃ c : Fin n → ℝ,
        (∀ i, a ≤ c i ∧ c i < b) ∧
        ∀ x ∈ Icc a b, ∃ i, x ∈ Icc (c i) b ∧ x - c i ≤ ρ := by
  let n := ⌈(b - a) / ρ⌉₊
  have hn : 0 < n := Nat.ceil_pos.mpr (div_pos (sub_pos.mpr hab) hρ)
  refine ⟨n, hn, (Nat.ceil_lt_add_one (div_nonneg (sub_pos.mpr hab).le hρ.le)).le,
    (fun i ↦ a + i.val * ρ), ?_, ?_⟩
  · intro i
    constructor
    · have : 0 ≤ (i.val : ℝ) * ρ := mul_nonneg (Nat.cast_nonneg _) hρ.le
      linarith
    · have hi : (i.val : ℝ) < (b - a) / ρ := Nat.lt_ceil.mp i.isLt
      have := (lt_div_iff₀ hρ).mp hi
      linarith
  · intro x hx
    by_cases he : x = a
    · refine ⟨⟨0, hn⟩, ?_, ?_⟩ <;> simp [he, hab.le, hρ.le]
    · have hxa : a < x := lt_of_le_of_ne hx.1 (Ne.symm he)
      let m := ⌈(x - a) / ρ⌉₊
      have hm : 0 < m := Nat.ceil_pos.mpr (div_pos (sub_pos.mpr hxa) hρ)
      have hmn : m ≤ n := Nat.ceil_mono (div_le_div_of_nonneg_right (by linarith [hx.2]) hρ.le)
      let i : Fin n := ⟨m - 1, by omega⟩
      have hi : (i.val : ℝ) + 1 = (m : ℝ) := by
        have : i.val + 1 = m := by dsimp [i]; omega
        exact_mod_cast this
      have hml : (x-a)/ρ ≤ (m : ℝ) := Nat.le_ceil _
      have hmu : (m : ℝ) < (x-a)/ρ + 1 :=
        Nat.ceil_lt_add_one (div_nonneg (sub_nonneg.mpr hx.1) hρ.le)
      have hil : (i.val : ℝ) * ρ ≤ x-a :=
        (le_div_iff₀ hρ).mp (by linarith)
      have hiu : x-a ≤ ((i.val : ℝ) + 1) * ρ :=
        (div_le_iff₀ hρ).mp (by linarith)
      refine ⟨i, ⟨by linarith, hx.2⟩, ?_⟩
      dsimp
      nlinarith

end MahlerLean
