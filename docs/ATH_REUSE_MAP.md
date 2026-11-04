# Reuse map: earlier MahlerLean vs new analytic-graphs proof

The earlier project is a substantial existing formal development, not a
blank slate. Reuse must be justified **by matching mathematical types**.

| Verified/previously developed module | Potential reuse | New work still needed |
| --- | --- | --- |
| `MahlerLean/RationalBlocks.lean` | Canonical reduced denominator blocks | Arbitrary-degree polynomial witness predicate |
| `MahlerLean/FareySeparation.lean` | Rational separation and interval packing | p-adic content classes and their stronger spacing |
| `MahlerLean/FareyCounting.lean` | Upper count for finite unions of intervals | New dyadic polynomial-height counting |
| `MahlerLean/FareyNumerators.lean`, `TotientBlock.lean` | Möbius inversion, quadratic rational supply | Quantitative uniformity when joining new witness sets |
| `MahlerLean/FiniteJetCover.lean`, `UniformJet.lean` | Compactness and finite derivative control | Polynomial-in-Y finite algebraic type (FT) |
| `MahlerLean/DeterminantRelations.lean`, `DeterminantVanishing.lean` | Determinant templates, integer-rank reasoning | Local reconstruction for shifted polynomial witnesses of degree 2k-1 |
| `MahlerLean/CurveTaylorBounds.lean` | Real Taylor controls | Lagrange interpolation of F(X,T_s(X)) with two heights |
| `MahlerLean/CantorTree.lean`, `CantorBranches.lean`, `CantorTopology.lean` | Compact binary trees; limit set topology and source Liouville mechanism | Simultaneous constraints for all m and measure-positive child selection |
| `MahlerLean/EntireRigidity.lean`, `CurrentTheoremOne.lean` | Previously proved entire-polynomial consequence | New theorem-1.2-to-corollary dependency route |

**Do not conflate results.** The old `proposition_5_1` bounds
degree-one rational target approximations and has terms
`Q² H^{-98}` and `Q^{17/10}`. The new Theorem 1.1 counts
small values of integer polynomials of **arbitrary bounded degree**,
with `w>2m-1` and `Q^{u₀}≤B≤Q^U`. Their statements differ,
so the old result cannot be cited as a proof of the new theorem.

The legacy work is reported as checked in `VALIDATION.md`, but a
new statement-level audit must still inspect what each imported
declaration *actually says*. Do not simply trust an old README badge.
