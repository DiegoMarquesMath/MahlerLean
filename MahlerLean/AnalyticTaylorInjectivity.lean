import MahlerLean.RationalFamilyIndependent

noncomputable section
namespace MahlerLean
open scoped Topology

/-- A scalar analytic function with zero derivatives of every order has zero germ. -/
theorem eventually_zero_of_all_iteratedDeriv_zero
    {g : ℝ → ℝ} {z : ℝ} (hg : AnalyticAt ℝ g z)
    (hz : ∀ n : ℕ, iteratedDeriv n g z = 0) :
    ∀ᶠ x in 𝓝 z, g x = 0 := by
  have hp := hg.hasFPowerSeriesAt
  have hseries : FormalMultilinearSeries.ofScalars ℝ
      (fun n ↦ iteratedDeriv n g z / n.factorial) = 0 := by
    ext n
    simp [hz, FormalMultilinearSeries.ofScalars]
  rw [hseries] at hp
  exact hp.eventually_eq_zero

/-- Every nonzero combination of the rational family has a nonzero Taylor derivative. -/
theorem rationalFamily_exists_nonzero_derivative
    {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (hne : U.Nonempty)
    (hconn : IsPreconnected U) (hf : AnalyticOnNhd ℝ f U)
    (hnr : ¬ IsRationalOn f U) (d : ℕ)
    (c : Fin (2 * (d + 1)) → ℝ) (hc : ∃ j, c j ≠ 0)
    {z : ℝ} (hz : z ∈ U) :
    ∃ n : ℕ, iteratedDeriv n (fun x ↦ ∑ j, c j * rationalFamily f d j x) z ≠ 0 := by
  by_contra h
  push_neg at h
  have ha : AnalyticOnNhd ℝ (fun x ↦ ∑ j, c j * rationalFamily f d j x) U :=
    Finset.analyticOnNhd_fun_sum _
      (fun j _ ↦ analyticOnNhd_const.mul (rationalFamily_analytic hf d j))
  have he := eventually_zero_of_all_iteratedDeriv_zero (ha z hz) h
  have hcoeff := rationalFamily_coeff_eq_zero_of_eventually_sum_eq_zero
    hU hne hconn hf hnr d c hz he
  obtain ⟨j, hj⟩ := hc
  exact hj (hcoeff j)

/-- A nonzero combination has a finite first nonzero Taylor derivative. -/
theorem rationalFamily_exists_first_nonzero_derivative
    {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (hne : U.Nonempty)
    (hconn : IsPreconnected U) (hf : AnalyticOnNhd ℝ f U)
    (hnr : ¬ IsRationalOn f U) (d : ℕ)
    (c : Fin (2 * (d + 1)) → ℝ) (hc : ∃ j, c j ≠ 0)
    {z : ℝ} (hz : z ∈ U) :
    ∃ n : ℕ,
      iteratedDeriv n (fun x ↦ ∑ j, c j * rationalFamily f d j x) z ≠ 0 ∧
      ∀ m < n, iteratedDeriv m (fun x ↦ ∑ j, c j * rationalFamily f d j x) z = 0 := by
  classical
  have h := rationalFamily_exists_nonzero_derivative hU hne hconn hf hnr d c hc hz
  refine ⟨Nat.find h, Nat.find_spec h, ?_⟩
  intro m hm
  exact not_not.mp (Nat.find_min h hm)

end MahlerLean
