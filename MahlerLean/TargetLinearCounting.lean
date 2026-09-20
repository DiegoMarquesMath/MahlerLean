import MahlerLean.DeterminantSublevelBridge
import MahlerLean.FareyCounting

/-!
Counting consequence of the target-linear determinant method.  Once every
maximal determinant vanishes, the rational source points share a normalized
relation; the disjoint uniform sublevel decomposition then feeds directly
into the Farey bound.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal

noncomputable section
namespace MahlerLean

/-- Uniform counting bound for a finite rational family after determinant
vanishing.  The target values are arbitrary real approximants here; arithmetic
denominator clearing is used upstream to establish `hdet`. -/
theorem exists_targetLinear_counting_bound_of_all_det_zero
    {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hf : AnalyticOnNhd ℝ f U) (d : ℕ)
    {A B : ℝ} (hAB : A ≤ B) (hJU : Icc A B ⊆ U)
    (hW : ∀ z ∈ Icc A B, rationalWronskian f d z ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∃ R : ℕ, 0 < R ∧
    ∃ eps0 : ℝ, 0 < eps0 ∧ eps0 < 1 ∧
      ∀ (S : Finset ℚ) (y : ℚ → ℝ) {Q : ℕ} {X δ : ℝ},
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
  obtain ⟨C, hC, R, hR, eps0, heps0, heps1, hbridge⟩ :=
    exists_uniform_sublevel_data_of_targetLinear_det_zero
      hU hf d hAB hJU hW
  refine ⟨C, hC, R, hR, eps0, heps0, heps1, ?_⟩
  intro S y Q X δ hQ hdet hX hx hxI hδ happrox hden hsmall
  obtain ⟨c, hc, hcpoints, hcover, htmeasure⟩ :=
    hbridge (fun r : ↑S ↦ (r : ℝ)) (fun r : ↑S ↦ y r)
      hdet hX
      (fun r ↦ hx r r.property)
      (fun r ↦ hxI r r.property)
      hδ (fun r ↦ happrox r r.property) hsmall
  obtain ⟨t, htcard, htconn, htdis, htcover⟩ := hcover
  let sublevel : Set ℝ :=
    {z | z ∈ Icc A B ∧
      ‖∑ j, c j * (z ^ (j.val / 2) * f z ^ (j.val % 2))‖ ≤
        (2 * (d + 1) : ℕ) * (X ^ d * δ)}
  have hunion : (⋃ E ∈ t, E) = sublevel := by
    ext z
    constructor
    · intro hz
      obtain ⟨E, hz⟩ := Set.mem_iUnion.mp hz
      obtain ⟨hEt, hzE⟩ := Set.mem_iUnion.mp hz
      exact (htcover z).mpr ⟨E, hEt, hzE⟩
    · intro hz
      obtain ⟨E, hEt, hzE⟩ := (htcover z).mp hz
      exact Set.mem_iUnion.mpr ⟨E, Set.mem_iUnion.mpr ⟨hEt, hzE⟩⟩
  have hcoverS : ∀ r ∈ S, ∃ E ∈ t, (r : ℝ) ∈ E := by
    intro r hr
    exact (htcover r).mp (hcpoints ⟨r, hr⟩)
  have hfinite : volume (⋃ E ∈ t, E) ≠ ∞ := by
    apply ne_top_of_le_ne_top
      (measure_Icc_lt_top (a := A) (b := B) (μ := volume)).ne
    apply measure_mono
    rw [hunion]
    intro z hz
    exact hz.1
  have hcount := rational_union_card_le t id S Q R hQ htcard htconn htdis
    hcoverS hden hfinite
  simp only [id_eq] at hcount
  rw [hunion] at hcount
  change volume.real sublevel ≤
      C * ((2 * (d + 1) : ℕ) * (X ^ d * δ)) ^
        (((2 * (d + 1) - 1 : ℕ) : ℝ)⁻¹) at htmeasure
  calc
    (S.card : ℝ) ≤
        4 * (Q : ℝ) ^ 2 * volume.real sublevel + R := hcount
    _ ≤ 4 * (Q : ℝ) ^ 2 *
          (C * ((2 * (d + 1) : ℕ) * (X ^ d * δ)) ^
            (((2 * (d + 1) - 1 : ℕ) : ℝ)⁻¹)) + R := by
      gcongr

end MahlerLean
