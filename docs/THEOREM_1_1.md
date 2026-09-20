# Theorem 1.1: entire-function rigidity

## Statement correspondence

The manuscript's Theorem 1.1 (label `thm:intro-mahler`) states that
an entire function F : ℂ → ℂ preserving all Liouville numbers belongs to ℝ[z].

The declaration `MahlerLean.theorem_1_1` in
[EntireRigidity.lean](../MahlerLean/EntireRigidity.lean) proves:

```lean
theorem theorem_1_1 {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hpres : ∀ x : ℝ, Liouville x → ∃ y : ℝ, Liouville y ∧ F x = y) :
    ∃ P : Polynomial ℝ, ∀ z : ℂ, F z = P.eval₂ Complex.ofRealHom z
```

Here complex differentiability everywhere is precisely the entire-function
hypothesis. The real arguments and values in the preservation hypothesis
are embedded in ℂ by the canonical coercion. The conclusion supplies an
actual polynomial over ℝ whose evaluation agrees with F on all of ℂ.
Thus it also excludes every transcendental entire function.

No real-axis, rationality, Wronskian or counting assumption is added.

## Proof

1. **Real rational rigidity.** Apply Theorem 1.2 contrapositively: a
   nonrational real-analytic function has a Liouville input whose image
   satisfies eventual target avoidance and hence is not Liouville.
2. **Real values on the axis.** The imaginary part of F vanishes on the
   dense set of real Liouville numbers, so continuity makes it vanish
   on the whole real axis.
3. **Analytic restriction.** Restrict the complex analytic function to
   real scalars and compose with the real embedding and real-part map.
4. **Complex continuation.** A rational expression on the real axis gives
   the entire identity QF − P = 0 on ℂ by the identity theorem.
5. **Pole cancellation.** Extract the polynomial gcd, cancel it using the
   analytic identity theorem, and obtain coprime real polynomials A,B
   with BF = A on ℂ. Coprimality rules out a complex zero of B. The
   fundamental theorem of algebra makes B constant; hence F is the
   real polynomial B(0)⁻¹A.

The six declarations in this module are included in `scripts/Audit.lean`.
Reproduction instructions and verification results are in
[VALIDATION.md](../VALIDATION.md).
