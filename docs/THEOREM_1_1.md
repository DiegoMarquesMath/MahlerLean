# Legacy declaration `theorem_1_1`: current Theorem 1.3

## Current manuscript numbering

The declaration `MahlerLean.theorem_1_1` predates the final renumbering of the
manuscript. It corresponds to **Theorem 1.3 (entire-function rigidity)** in
*Arithmetic Rigidity of Analytic Functions and Mahler's Problem on Liouville Numbers*.

The current Theorem 1.3 states that an entire function
$F:\mathbb C\to\mathbb C$ preserving all Liouville numbers belongs to
$\mathbb R[z]$. In particular, no transcendental entire function has
Maillet's property.

A numbering-stable alias is now provided as
`MahlerLean.current_theorem_1_3` in
[CurrentTheoremOne.lean](../MahlerLean/CurrentTheoremOne.lean).

## Legacy Lean declaration

[EntireRigidity.lean](../MahlerLean/EntireRigidity.lean) proves:

```lean
theorem theorem_1_1 {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hpres : ∀ x : ℝ, Liouville x → ∃ y : ℝ, Liouville y ∧ F x = y) :
    ∃ P : Polynomial ℝ, ∀ z : ℂ, F z = P.eval₂ Complex.ofRealHom z
```

Complex differentiability everywhere is precisely the entire-function
hypothesis. The conclusion supplies an actual polynomial over $\mathbb R$
agreeing with $F$ on all of $\mathbb C$.

## Proof structure

1. **Local rational rigidity.** Preservation of all Liouville numbers forces
   rationality of the real-analytic restriction.
2. **Real values on the axis.** Density of real Liouville numbers and
   continuity imply $F(\mathbb R)\subseteq\mathbb R$.
3. **Complex continuation.** The rational identity on the real axis extends to
   $\mathbb C$.
4. **Absence of poles.** Coprimality and the fundamental theorem of algebra
   force the denominator to be constant.

Thus $F\in\mathbb R[z]$.

## Relation to current Theorem 1.1

The stronger local Cantor-set theorem is now fully formalized as
`MahlerLean.current_theorem_1_1`. Theorem 1.3 does not logically require the
Cantor strengthening: the single-point quantitative escape already suffices
for Corollary 1.2 and hence for entire-function rigidity.

The declarations are included in `scripts/Audit.lean`.
