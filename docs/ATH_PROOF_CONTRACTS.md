# Paper-to-Lean proof contracts

The following specifications reflect the original manuscript and adversarial
audit. **Recheck against `ATH_rev.tex` before formalizing**, because the revised
Mac files were not available at creation of this document.

## Notation and domain

- `f : I → ℝ`, where `I` is an open real interval and `J ⊂⊂ I`
  is a nondegenerate compact interval.
- `F_Q(J)` contains **reduced** `p/q ∈ J` with `Q ≤ q < 2Q`.
  Count each rational once, regardless of the number of witnesses.
- `P ∈ ℤ[Y]` is nonzero, `deg P ≤ m`,
  `B ≤ H(P) < 2B`, with `H(P)` the maximum absolute coefficient.
- The witness inequality is `|P(f(p/q))| ≤ L B^{-w}`.
  Include exact polynomial zeros and nonprimitive polynomials.

## Two-height count — new Theorem 1.1

For fixed real-analytic `f` transcendental over `ℝ(X)`,
`m ≥ 1`, `w > 2m-1`, `0 < u₀ ≤ U`, `L > 0`, and a compact `J`:
there exist `η > 0`, `C > 0`, and `Q₀` such that
for all `Q ≥ Q₀` and all `B` with `Q^{u₀} ≤ B ≤ Q^U`,
the exceptional rational set has at most `C Q^{2-η}` elements.

**Quantifier order:** fixed parameters and f,J → η,C,Q₀ → Q,B.

## Uniform finite-type count — Theorem 2.1

For a family of smooth functions, require **common** finite-type
constants and derivative bounds for each requested bidegree/order;
then η,C,Q₀ do not depend on the member of the family.
Do not replace these assumptions by memberwise finite type.

## Reconstruction / propagation contracts

- **3.1:** For `M ≥ 1, w > M`, local rows admit one nonzero integral
  relation of controlled X-degree and polynomial height, regardless of the
  number of rows. Include rank zero and fewer-than-N-rows cases.
- **3.2:** Given irreducible degree-k primitive witnesses,
  reconstruct one primitive `F ∈ ℤ[X,Y]` of Y-degree exactly k, with
  coprime X-coefficients; discard at most `a` rational arguments.
- **4.1:** The content bound must be uniform in F, E, G, and Q after
  fixing D,k,ζ: `O(H(F)^ζ (1 + |E| Q² G^{-1/D}))`.
  Prove D=0 separately and handle both projective charts for D≥1.
- **4.2:** Use an *integral* Sylvester resultant; keep the k,h-1
  exponents and the constant specialization case.
- **5.1:** Preserve a single `F` while expanding intervals.
  Retain original witness proportionality for every required rational.
  Return density, arbitrarily many fixed separated good nodes, and the
  final height estimate; no dependence on earlier extrapolation losses.

## Diophantine consequences — Theorem 1.2

Every nonempty open subinterval contains one Cantor set K of Liouville
numbers such that *every* ξ ∈ K has transcendental image f(ξ),
`w_m(f(ξ)) ≤ 2m-1` for **all m simultaneously**, and
`μ(f(ξ)) = 2`. Formalize the usual nonzero polynomial evaluation in
the definition of `w_m`; exclude algebraic values by a separate argument
using large integer multiples of a minimal polynomial.

## Arithmetic descent — Theorem 1.4

For an algebraic real-analytic branch with primitive minimal equation
`S(X,Y)` of bidegree `(d,m)`, both positive, the line `ℝS` is
defined over ℚ if and only if a positive proportion of reduced rationals
on arbitrarily large Q have algebraic approximations of degree ≤m,
height ≤C Q^d and error ≤Q^{-40md}. Critical: proving
projective convergence alone is insufficient; use the content estimate
and positive density to bound the integer height of F.

## Corollary 1.3 — entire rigidity

For entire F, if F maps every real Liouville number to a real
Liouville number, then F is a polynomial with real coefficients.
This exact *statement* already follows from the legacy Lean project.
The *new derivation via Theorem 1.2* remains an additional formal goal.

## Required edge cases

m=1; D=0; degree drop on specialization; exact zeros;
reducible and repeated factors; witnesses with H(P) much smaller
than the original B; all dyadic endpoints; arbitrary translation
families; nested Cantor branches; all quantifiers at the height boundary.
