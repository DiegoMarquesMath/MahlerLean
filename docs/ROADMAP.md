# Proof roadmap

The local quantitative Theorem 1.2 is assembled in
[`MahlerLean.theorem_1_2`](../MahlerLean/IrrationalityExponent.lean).
The proof follows this dependency structure:

1. **Arithmetic supply and packing.** Farey separation, counting in interval
   components and source supply with cF = 1/4.
2. **Uniform analytic estimates.** Wronskian localization, normalized jets,
   finite interval covers and uniform sublevel measure bounds.
3. **Two-height counting.** Arithmetic determinant lower bounds, analytic
   determinant decay with multilinear perturbations, rank-to-counting,
   source cells, small and large dyadic target blocks. These prove Proposition
   5.1 with the original margin and uniformity in H.
4. **Infinite fusion.** Safe centers, nested intervals and source/target
   invariants give a Liouville point and eventual target avoidance.
5. **Original analytic hypotheses.** Local derivative bounds follow from
   nonconstancy. Nonrationality gives independence of the rational family;
   an adapted Taylor basis and the Wronskian leading term give nontriviality.
6. **Quantitative conclusion.** The exact infinitely-many-pairs definition
   of the irrationality exponent converts avoidance into μ(f(ξ)) ≤ 100.

No mathematical intermediate lemma remains open for this formal statement
of Theorem 1.2. Statement correspondence is recorded in
[THEOREM_1_2.md](THEOREM_1_2.md) and [STEP14_PT.md](STEP14_PT.md).
The actual validation performed is recorded in [VALIDATION.md](../VALIDATION.md).

## Separate future work

- Formalize the rational-rigidity corollary and the entire-function
  consequence, Theorem 1.1.
- Formalize the independent Section 7 statements if desired.
- Prepare a tagged archival release and optional public blueprint site for citation.

These are separate from the completed mathematical dependency chain for
Proposition 5.1 and Theorem 1.2. Historical `STEP*.md` files retain their
checkpoint descriptions and are not the current list of pending results.
