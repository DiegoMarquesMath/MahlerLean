# Legacy declaration \`theorem_1_1\`: current Theorem 1.3

## Current manuscript numbering

The declaration \`MahlerLean.theorem_1_1\` predates the final renumbering of the
manuscript. It now corresponds to **Theorem 1.3 (entire-function rigidity)** in

*Arithmetic Rigidity of Analytic Functions and Mahler's Problem on Liouville Numbers*.

The current Theorem 1.3 states that an entire function
\(F:\mathbb C\to\mathbb C\) preserving all Liouville numbers belongs to
\(\mathbb R[z]\). In particular, no transcendental entire function has
Maillet's property.

## Lean declaration

The declaration in [EntireRigidity.lean](../MahlerLean/EntireRigidity.lean) is:

\`\`\`lean
theorem theorem_1_1 {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hpres : ∀ x : ℝ, Liouville x → ∃ y : ℝ, Liouville y ∧ F x = y) :
    ∃ P : Polynomial ℝ, ∀ z : ℂ, F z = P.eval₂ Complex.ofRealHom z
\`\`\`

Complex differentiability everywhere is exactly the entire-function hypothesis.
The preservation hypothesis says that every real Liouville input is sent to a
real Liouville value. The conclusion supplies an actual polynomial over
\(\mathbb R\) agreeing with \(F\) on all of \(\mathbb C\).

No extra real-axis rationality, Wronskian, or counting hypothesis appears in the
final statement.

## Proof structure

1. **Local rational rigidity.** The already verified single-point quantitative
   escape statement implies contrapositively that any real-analytic function
   preserving all Liouville numbers must be rational on its interval. In the
   current manuscript this is Corollary 1.2.
2. **Real values on the axis.** The imaginary part of \(F\) vanishes on the
   dense set of real Liouville numbers, hence on all of \(\mathbb R\).
3. **Analytic restriction.** Restrict the entire function to the real axis.
4. **Complex continuation.** A rational identity on \(\mathbb R\) yields
   \(QF-P\equiv0\) on \(\mathbb C\) by the identity theorem.
5. **Absence of poles.** Coprimality and the fundamental theorem of algebra
   force \(Q\) to be constant.

Thus \(F\in\mathbb R[z]\).

## Relation to the current Theorem 1.1

The current Theorem 1.1 is the stronger local Cantor-set theorem and is being
completed on the \`cantor-refinement\` branch. The current Theorem 1.3 does not
depend on the Cantor strengthening: the verified single-point escape statement
already suffices for Corollary 1.2 and hence for entire-function rigidity.

The declarations in this module are included in \`scripts/Audit.lean\`.
Reproduction instructions and verification results are in
[VALIDATION.md](../VALIDATION.md).
