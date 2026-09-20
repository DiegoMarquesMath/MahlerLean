import MahlerLean.RationalRelation

noncomputable section
namespace MahlerLean
open Polynomial
open scoped Topology

/-- The even/odd coefficients of the target-degree-one family, as a polynomial. -/
def relationPolynomial {d : ℕ} (c : Fin (2 * (d + 1)) → ℝ) (e : ℕ) : Polynomial ℝ :=
  ∑ j, if j.val % 2 = e then Polynomial.monomial (j.val / 2) (c j) else 0

theorem relationPolynomial_coeff {d : ℕ} (c : Fin (2 * (d + 1)) → ℝ)
    (j : Fin (2 * (d + 1))) :
    (relationPolynomial c (j.val % 2)).coeff (j.val / 2) = c j := by
  classical
  simp only [relationPolynomial, finset_sum_coeff]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hkj
    by_cases he : k.val % 2 = j.val % 2
    · have hd : k.val / 2 ≠ j.val / 2 := by
        intro hd
        apply hkj
        apply Fin.ext
        omega
      simp [he, Polynomial.coeff_monomial, hd]
    · simp [he]
  · simp

theorem relationPolynomial_eval {d : ℕ} (c : Fin (2 * (d + 1)) → ℝ)
    (f : ℝ → ℝ) (x : ℝ) :
    (relationPolynomial c 0).eval x + (relationPolynomial c 1).eval x * f x =
      ∑ j, c j * rationalFamily f d j x := by
  classical
  simp only [relationPolynomial, Polynomial.eval_finset_sum, Finset.sum_mul,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have hj : j.val % 2 = 0 ∨ j.val % 2 = 1 := by omega
  rcases hj with hj | hj <;>
    simp [hj, rationalFamily, Polynomial.eval_monomial, mul_comm, mul_left_comm]

/-- Nonrationality implies independence of the exact family restricted to U. -/
theorem rationalFamily_linearIndependent_of_not_rational
    {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (hne : U.Nonempty)
    (hconn : IsPreconnected U) (hf : AnalyticOnNhd ℝ f U)
    (hnr : ¬ IsRationalOn f U) (d : ℕ) :
    LinearIndependent ℝ (fun j : Fin (2 * (d + 1)) ↦
      fun x : U ↦ rationalFamily f d j x) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc j
  have hrel : ∀ x ∈ U,
      (relationPolynomial c 0).eval x + (relationPolynomial c 1).eval x * f x = 0 := by
    intro x hx
    rw [relationPolynomial_eval]
    have h := congrFun hc ⟨x, hx⟩
    simpa using h
  obtain ⟨hA, hB⟩ := polynomial_relation_eq_zero_of_not_rational hU hne hconn hf hnr
    (relationPolynomial c 0) (relationPolynomial c 1) hrel
  have hj : j.val % 2 = 0 ∨ j.val % 2 = 1 := by omega
  have h := relationPolynomial_coeff c j
  rcases hj with hj | hj
  · rw [hj, hA] at h
    simpa using h.symm
  · rw [hj, hB] at h
    simpa using h.symm

/-- Independence also holds for analytic germs at every point of U. -/
theorem rationalFamily_coeff_eq_zero_of_eventually_sum_eq_zero
    {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (hne : U.Nonempty)
    (hconn : IsPreconnected U) (hf : AnalyticOnNhd ℝ f U)
    (hnr : ¬ IsRationalOn f U) (d : ℕ)
    (c : Fin (2 * (d + 1)) → ℝ) {z : ℝ} (hz : z ∈ U)
    (hzero : ∀ᶠ x in 𝓝 z, (∑ j, c j * rationalFamily f d j x) = 0) :
    ∀ j, c j = 0 := by
  have ha : AnalyticOnNhd ℝ (fun x ↦ ∑ j, c j * rationalFamily f d j x) U := by
    exact Finset.analyticOnNhd_fun_sum _
      (fun j _ ↦ analyticOnNhd_const.mul (rationalFamily_analytic hf d j))
  have hglobal := ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hz hzero
  apply (Fintype.linearIndependent_iff.mp
    (rationalFamily_linearIndependent_of_not_rational hU hne hconn hf hnr d)) c
  funext x
  simpa using hglobal x.property

end MahlerLean
