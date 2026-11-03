import MahlerLean.FareyCounting
import MahlerLean.CurrentTheoremOne

/-!
# Explicit reuse from MahlerLean

These are theorems already established in the older project.
The entire-function corollary is obtained from the older (weaker)
rigidity route, not yet as a corollary of the new arbitrary-degree
counting theorem. The distinction matters for the proof coverage map.
-/

noncomputable section
namespace AnalyticGraphs

/-- Farey spacing, reused without strengthening its assumptions. -/
theorem reducedRationalSpacing (r s : ℚ) (hrs : r ≠ s) :
    1 / ((r.den : ℝ) * (s.den : ℝ)) ≤ |(r : ℝ) - (s : ℝ)| :=
  MahlerLean.rational_separation r s hrs

/-- Mahler's entire-function rigidity, obtained from the existing
formalization. This statement matches the new paper's Corollary 1.3,
but is not yet derived from its Theorem 1.2 inside Lean. -/
theorem entireRigidity
    {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hpres : ∀ x : ℝ, Liouville x →
      ∃ y : ℝ, Liouville y ∧ F x = y) :
    ∃ P : Polynomial ℝ, ∀ z : ℂ,
      F z = P.eval₂ Complex.ofRealHom z :=
  MahlerLean.current_theorem_1_3 hF hpres

end AnalyticGraphs
