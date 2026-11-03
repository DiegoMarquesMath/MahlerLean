import Mathlib
import MahlerLean.RationalBlocks

/-!
# Basic witnesses for the analytic-graphs project

These are *definitions*, not the counting theorem.
They encode integer polynomials, naive coefficient height, exact zeros,
independent denominator and polynomial-height scales, and counting each
rational argument only once.
-/

noncomputable section
namespace AnalyticGraphs

/-- Naive height: maximum absolute value of the integer coefficients. -/
def naiveHeight (P : Polynomial ℤ) : ℕ :=
  P.support.sup (fun i => (P.coeff i).natAbs)

/-- Evaluate an integer polynomial at a real ordinate. -/
def polynomialValue (P : Polynomial ℤ) (y : ℝ) : ℝ :=
  P.eval₂ (Int.castRingHom ℝ) y

/-- The precise small-value witness at a rational argument.

B, w and L are independent of the denominator block Q. Exact zeros
are included; P is required to be nonzero. -/
def HasPolynomialWitness (f : ℝ → ℝ) (r : ℚ)
    (m : ℕ) (B w L : ℝ) : Prop :=
  ∃ P : Polynomial ℤ,
    P ≠ 0 ∧
    P.natDegree ≤ m ∧
    B ≤ (naiveHeight P : ℝ) ∧
    (naiveHeight P : ℝ) < 2 * B ∧
    |polynomialValue P (f (r : ℝ))| ≤ L * B ^ (-w)

/-- Exceptional rational arguments in [l,u], canonical reduced
denominators in [Q,2Q). Each argument is counted once. -/
def exceptionalArguments (f : ℝ → ℝ) (l u : ℝ)
    (Q m : ℕ) (B w L : ℝ) : Finset ℚ := by
  classical
  exact (MahlerLean.sourceFractions l u Q).filter
    (fun r => HasPolynomialWitness f r m B w L)

theorem mem_exceptionalArguments (f : ℝ → ℝ) (l u : ℝ)
    (Q m : ℕ) (B w L : ℝ) (r : ℚ) :
    r ∈ exceptionalArguments f l u Q m B w L ↔
      r ∈ MahlerLean.sourceFractions l u Q ∧
        HasPolynomialWitness f r m B w L := by
  classical
  simp [exceptionalArguments]

end AnalyticGraphs
