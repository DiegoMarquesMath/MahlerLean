import MahlerLean.AnalyticDerivativeInterval
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.RingTheory.PrincipalIdealDomain

noncomputable section
namespace MahlerLean
open Set Polynomial

/-- Rationality on U with a denominator that is nonzero everywhere on U. -/
def IsRationalOn (f : ℝ → ℝ) (U : Set ℝ) : Prop :=
  ∃ P Q : Polynomial ℝ, Q ≠ 0 ∧
    (∀ x ∈ U, Q.eval x ≠ 0) ∧ ∀ x ∈ U, f x = P.eval x / Q.eval x

/-- A polynomial vanishing on a nonempty real open set is zero. -/
theorem polynomial_eq_zero_on_open {U : Set ℝ} (hU : IsOpen U) (hne : U.Nonempty)
    (P : Polynomial ℝ) (hP : ∀ x ∈ U, P.eval x = 0) : P = 0 := by
  obtain ⟨a, b, hab, hsub⟩ := hU.exists_Ioo_subset hne
  apply P.eq_zero_of_infinite_isRoot
  exact (Set.Ioo_infinite hab).mono (fun x hx ↦ hP x (hsub hx))

/-- Cancelling the polynomial gcd removes all apparent poles of an analytic relation. -/
theorem isRationalOn_of_polynomial_relation
    {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (hne : U.Nonempty)
    (hconn : IsPreconnected U) (hf : AnalyticOnNhd ℝ f U)
    (A B : Polynomial ℝ) (hB : B ≠ 0)
    (hrel : ∀ x ∈ U, A.eval x + B.eval x * f x = 0) : IsRationalOn f U := by
  obtain ⟨P, Q, hA, hBQ, hcop⟩ := extract_gcd A B
  have hD : gcd A B ≠ 0 := by
    intro h
    apply hB
    rw [hBQ, h, zero_mul]
  have han (R : Polynomial ℝ) : AnalyticOnNhd ℝ (fun x ↦ R.eval x) U :=
    (AnalyticOnNhd.eval_polynomial R).mono (subset_univ U)
  have hprod : ∀ x ∈ U,
      (gcd A B).eval x • (P.eval x + Q.eval x * f x) = 0 := by
    intro x hx
    have h := hrel x hx
    have ha : A.eval x = (gcd A B).eval x * P.eval x := by
      exact (congrArg (Polynomial.eval x) hA).trans (Polynomial.eval_mul)
    have hb : B.eval x = (gcd A B).eval x * Q.eval x := by
      exact (congrArg (Polynomial.eval x) hBQ).trans (Polynomial.eval_mul)
    rw [ha, hb] at h
    change (gcd A B).eval x * (P.eval x + Q.eval x * f x) = 0
    nlinarith [h]
  have hPQ : ∀ x ∈ U, P.eval x + Q.eval x * f x = 0 := by
    rcases (han (gcd A B)).eq_zero_or_eq_zero_of_smul_eq_zero
      ((han P).add ((han Q).mul hf)) hprod hconn with hzero | hzero
    · exact (hD (polynomial_eq_zero_on_open hU hne _ hzero)).elim
    · exact hzero
  have hcp : IsCoprime P Q := (gcd_isUnit_iff_isRelPrime.mp hcop).isCoprime
  have hQ : ∀ x ∈ U, Q.eval x ≠ 0 := by
    intro x hx hz
    have hp : P.eval x = 0 := by simpa [hz] using hPQ x hx
    rcases Polynomial.aeval_ne_zero_of_isCoprime hcp x with h | h
    · exact h (by simpa using hp)
    · exact h (by simpa using hz)
  refine ⟨-P, Q, ?_, hQ, ?_⟩
  · intro hz
    obtain ⟨x, hx⟩ := hne
    exact hQ x hx (by simp [hz])
  · intro x hx
    apply (eq_div_iff (hQ x hx)).mpr
    simp only [Polynomial.eval_neg]
    nlinarith [hPQ x hx]

/-- Nonrationality excludes every nontrivial target-degree-one polynomial relation. -/
theorem polynomial_relation_eq_zero_of_not_rational
    {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (hne : U.Nonempty)
    (hconn : IsPreconnected U) (hf : AnalyticOnNhd ℝ f U)
    (hnr : ¬ IsRationalOn f U) (A B : Polynomial ℝ)
    (hrel : ∀ x ∈ U, A.eval x + B.eval x * f x = 0) : A = 0 ∧ B = 0 := by
  have hB : B = 0 := by
    by_contra hB
    exact hnr (isRationalOn_of_polynomial_relation hU hne hconn hf A B hB hrel)
  refine ⟨polynomial_eq_zero_on_open hU hne A ?_, hB⟩
  intro x hx
  simpa [hB] using hrel x hx

/-- Nonrationality supplies the nonconstancy input of local escape. -/
theorem nonconstant_of_not_rational
    {f : ℝ → ℝ} {U : Set ℝ} (hne : U.Nonempty) (hnr : ¬ IsRationalOn f U) :
    ∃ x ∈ U, ∃ y ∈ U, f x ≠ f y := by
  by_contra h
  push_neg at h
  obtain ⟨z, hz⟩ := hne
  apply hnr
  refine ⟨Polynomial.C (f z), 1, one_ne_zero, ?_, ?_⟩
  · simp
  · intro x hx
    simpa using h x hx z hz

/-- The remaining hypothesis beyond nonrationality is Wronskian nontriviality. -/
theorem exists_escape_of_not_rational_and_wronskians
    {f : ℝ → ℝ} {U V : Set ℝ} (hU : IsOpen U) (hconn : IsPreconnected U)
    (hf : AnalyticOnNhd ℝ f U) (hnr : ¬ IsRationalOn f U)
    (hW : ∀ d : ℕ, 2 ≤ d → ∃ y ∈ U, rationalWronskian f d y ≠ 0)
    (hV : IsOpen V) (hne : V.Nonempty) (hVU : V ⊆ U) :
    ∃ x : ℝ, ∃ B : ℕ, x ∈ V ∧ 2 ≤ B ∧
      Liouville x ∧ PaperLiouville x ∧
      EventualTargetAvoidance (f x) 100 B ∧ ¬ Liouville (f x) := by
  exact exists_escape_in_open_of_analytic_wronskians hU hconn hf
    (nonconstant_of_not_rational (hne.mono hVU) hnr) hW hV hne hVU

end MahlerLean
