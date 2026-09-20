import MahlerLean.TargetLinearCounting

open Set
noncomputable section
namespace MahlerLean

/-- One set of counting constants for the entire finite degree range. -/
theorem exists_uniform_degree_counting_data
    {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hf : AnalyticOnNhd ℝ f U) (D : ℕ) (hD : 2 ≤ D)
    {A B : ℝ} (hAB : A ≤ B) (hJU : Icc A B ⊆ U)
    (hW : ∀ d : ℕ, 2 ≤ d → d ≤ D →
      ∀ z ∈ Icc A B, rationalWronskian f d z ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∃ R : ℕ, 0 < R ∧
    ∃ eps0 : ℝ, 0 < eps0 ∧ eps0 < 1 ∧
      ∀ d : ℕ, 2 ≤ d → d ≤ D → ∀ (S : Finset ℚ) (y : ℚ → ℝ) {Q : ℕ} {X δ : ℝ},
        0 < Q →
        (∀ rows : Fin (2 * (d + 1)) → ↑S,
          (targetLinearMatrix d
            (fun i ↦ (rows i : ℝ))
            (fun i ↦ y (rows i))).det = 0) →
        1 ≤ X → (∀ r ∈ S, |(r : ℝ)| ≤ X) →
        (∀ r ∈ S, (r : ℝ) ∈ Icc A B) →
        0 ≤ δ → (∀ r ∈ S, |y r - f r| ≤ δ) →
        (∀ r ∈ S, r.den < 2 * Q) →
        (2 * (d + 1) : ℕ) * (X ^ d * δ) < eps0 →
        (S.card : ℝ) ≤
          4 * (Q : ℝ) ^ 2 *
            (C * ((2 * (d + 1) : ℕ) * (X ^ d * δ)) ^
              (((2 * (d + 1) - 1 : ℕ) : ℝ)⁻¹)) + R := by
  classical
  let I := Fin (D - 1)
  let i₀ : I := ⟨0, by omega⟩
  have hex (i : I) := exists_targetLinear_counting_bound_of_all_det_zero hU hf
    (i.val + 2) hAB hJU (hW _ (by omega) (by have := i.isLt; omega))
  choose C hC R hR eps heps heps1 hb using hex
  have hne : (Finset.univ : Finset I).Nonempty := ⟨i₀, Finset.mem_univ _⟩
  let e := Finset.univ.inf' hne eps
  have he : 0 < e := (Finset.lt_inf'_iff hne).mpr (fun i _ ↦ heps i)
  have hei (i : I) : e ≤ eps i := Finset.inf'_le eps (Finset.mem_univ i)
  have hCi (i : I) : C i ≤ ∑ j, C j :=
    Finset.single_le_sum (fun j _ ↦ (hC j).le) (Finset.mem_univ i)
  have hRi (i : I) : R i ≤ ∑ j, R j :=
    Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
  refine ⟨∑ i, C i, (hC i₀).trans_le (hCi i₀),
    ∑ i, R i, (hR i₀).trans_le (hRi i₀), e, he,
    (hei i₀).trans_lt (heps1 i₀), ?_⟩
  intro d hd2 hdD S y Q X δ hQ hdet hX hx hxI hδ herr hden hsmall
  let i : I := ⟨d - 2, by omega⟩
  have hi : i.val + 2 = d := by dsimp [i]; omega
  have hb' := hb i
  rw [hi] at hb'
  have hc := hb' S y hQ hdet hX hx hxI hδ herr hden (hsmall.trans_le (hei i))
  refine hc.trans ?_
  have hp : 0 ≤ ((2 * (d + 1) : ℕ) * (X ^ d * δ)) ^
      (((2 * (d + 1) - 1 : ℕ) : ℝ)⁻¹) := Real.rpow_nonneg (by positivity) _
  exact add_le_add (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (hCi i) hp) (by positivity)) (by exact_mod_cast hRi i)

end MahlerLean
