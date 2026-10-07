# Arithmetic Rigidity of Analytic Functions and Mahler's Problem on Liouville Numbers

[![Lean verification](https://github.com/DiegoMarquesMath/MahlerLean/actions/workflows/lean.yml/badge.svg?branch=cantor-refinement)](https://github.com/DiegoMarquesMath/MahlerLean/actions/workflows/lean.yml)

Lean 4 formalization of the analytic-rigidity core of Diego Marques's manuscript
[*Arithmetic Rigidity of Analytic Functions and Mahler's Problem on Liouville Numbers*](paper/main.pdf).

> **Cantor refinement.**
> This branch upgrades the already verified single-point escape theorem to the
> full Cantor-set conclusion of the current Theorem 1.1. The arithmetic part of
> the branch is already in place and passing CI; the remaining work is the final
> topological package and theorem-level assembly.

## Main results

### Theorem 1.1 — Local quantitative rigidity

Let \(U\subseteq\mathbb R\) be an open interval and let \(f:U\to\mathbb R\)
be real analytic. Suppose that \(f\) is not the restriction to \(U\) of a
rational function in \(\mathbb R(x)\) without poles on \(U\).

Then every nonempty open subinterval \(V\subseteq U\) contains a Cantor set
\(K\subseteq V\) of Liouville numbers such that

\[
\mu(f(\xi))\le 100 \qquad (\xi\in K).
\]

Moreover, one cutoff \(b_0\ge 2\) works simultaneously on the whole Cantor set:

\[
\left|f(\xi)-\frac{a}{b}\right|>b^{-100}
\]

for every \(\xi\in K\), every \(a\in\mathbb Z\), and every integer
\(b\ge b_0\).

On this branch the binary fusion tree, compact level sets, coherent branches,
Liouville property, common target cutoff, and the bound
\(\mu(f(\xi))\le100\) for every point of the limit set are already formalized
and passing CI. The remaining upgrade is to package perfectness and total
disconnectedness and expose the full theorem under the current manuscript
numbering.

### Corollary 1.2 — Local rational rigidity

If a real-analytic function \(f:U\to\mathbb R\) satisfies

\[
f(\mathcal L\cap U)\subseteq \mathcal L,
\]

then \(f\) is the restriction to \(U\) of a rational function in
\(\mathbb R(x)\) with no pole on \(U\).

### Theorem 1.3 — Entire-function rigidity

If an entire function \(F:\mathbb C\to\mathbb C\) satisfies

\[
F(\mathcal L)\subseteq \mathcal L,
\]

then \(F\in\mathbb R[z]\). In particular, no transcendental entire function
has Maillet's property.

This gives a negative answer, in the entire setting, to a problem posed by
Mahler in 1984.

### Proposition 5.1 — Two-height counting

The formalization includes the uniform two-height counting estimate on analytic
graphs, with source and target denominator scales treated independently and
uniformity in the lower target cutoff.

## Correspondence with the Lean development

| Current manuscript result | Lean declaration | Source | Status |
| --- | --- | --- | --- |
| Theorem 1.1, single-point quantitative core | \`MahlerLean.theorem_1_2\` | [IrrationalityExponent.lean](MahlerLean/IrrationalityExponent.lean) | Verified |
| Theorem 1.1, binary successor construction | \`MahlerLean.exists_binary_fusion_transition\` | [CantorFusion.lean](MahlerLean/CantorFusion.lean) | Verified |
| Theorem 1.1, binary tree and compact limit set | \`MahlerLean.cantorLimitSet\` | [CantorTree.lean](MahlerLean/CantorTree.lean) | Verified |
| Theorem 1.1, branch arithmetic | \`cantorLimitSet_liouville\`, \`cantorLimitSet_target_avoidance\`, \`cantorLimitSet_irrationalityExponent_le\` | [CantorBranches.lean](MahlerLean/CantorBranches.lean) | Verified |
| Theorem 1.1, subtree nonemptiness | \`MahlerLean.cantorLimitSet_meets_node\` | [CantorSubtree.lean](MahlerLean/CantorSubtree.lean) | Verified |
| Theorem 1.1, perfectness and total disconnectedness | forthcoming final topology module | — | In progress |
| Corollary 1.2 | \`MahlerLean.rationalOn_of_preserves_liouville\` | [EntireRigidity.lean](MahlerLean/EntireRigidity.lean) | Verified |
| Theorem 1.3 | \`MahlerLean.theorem_1_1\` (legacy declaration name) | [EntireRigidity.lean](MahlerLean/EntireRigidity.lean) | Verified |
| Proposition 5.1 | \`MahlerLean.proposition_5_1\` | [TwoHeightCounting.lean](MahlerLean/TwoHeightCounting.lean) | Verified |

The declaration names \`theorem_1_1\` and \`theorem_1_2\` predate the current
manuscript renumbering. Compatibility aliases matching the final paper numbering
will be added with the completed Cantor refinement.

## Additional manuscript results

The current manuscript also contains two independent Section 7 results:

- **Theorem 1.4 (Möbius rigidity).** A real Möbius transformation has Maillet's
  property if and only if it belongs to \(\mathbb Q(x)\).
- **Theorem 1.5 (nonlinear sharpness).** There exist continuum many positive
  transcendental real numbers \(\sigma\) such that
  \(\sigma\xi^m\in\mathcal L\) for every \(\xi\in\mathcal L\) and every
  integer \(m\ge2\).

These Section 7 results are mathematically independent of the analytic
two-height argument and remain outside the scope of this Lean project.

## Cantor-refinement structure

The upgrade is split into four modules:

- [CantorFusion.lean](MahlerLean/CantorFusion.lean): two separated successors
  from every admissible fusion stage;
- [CantorTree.lean](MahlerLean/CantorTree.lean): binary recursion, compact level
  sets and the global limit set;
- [CantorBranches.lean](MahlerLean/CantorBranches.lean): unique coherent branch,
  Liouville approximation, common target cutoff and irrationality exponent;
- [CantorSubtree.lean](MahlerLean/CantorSubtree.lean): every node interval
  contains a point of the global limit set.

The remaining topological step is tracked in
[docs/CANTOR_REFINEMENT.md](docs/CANTOR_REFINEMENT.md).

## Proof structure

| Component | Role in the proof |
| --- | --- |
| Farey estimates | Supply reduced rational source points and control their number in unions of intervals. |
| Uniform analytic estimates | Control sublevel sets through Wronskians, jets and finite covers. |
| Two-height counting | Combine analytic and arithmetic determinant bounds to prove Proposition 5.1. |
| Single-branch fusion | Construct one Liouville point whose image avoids very good rational approximations. |
| Binary fusion | Split every admissible successor into two separated children. |
| Compact binary tree | Form the decreasing level sets and the limit set \(K\). |
| Branch arithmetic | Prove every point of \(K\) is Liouville and satisfies the common target-avoidance bound. |
| Topological completion | Prove \(K\) perfect and totally disconnected. |
| Entire-function rigidity | Deduce Theorem 1.3 from local rational rigidity. |

## Verification

All currently marked **Verified** declarations pass the branch build and axiom
audit through GitHub Actions.

To reproduce the verification:

\`\`\`bash
lake exe cache get
bash scripts/check.sh
\`\`\`

The project pins Lean 4.24.0 and mathlib v4.24.0.

## Scope

The intended completed formalization covers:

- Proposition 5.1;
- the full current Theorem 1.1, including its Cantor-set strengthening;
- Corollary 1.2;
- Theorem 1.3.

The independent Section 7 results, including Theorems 1.4 and 1.5, remain
outside the present formalization.

## Citation

After the Cantor refinement is completely verified, the manuscript may use:

\`\`\`latex
A machine-checked Lean~4 formalization of Proposition~5.1 and of the complete
proof of Theorems~1.1 and~1.3, including the Cantor-set refinement in
Theorem~1.1, is available at
\url{https://github.com/DiegoMarquesMath/MahlerLean}.
\`\`\`

For reproducibility, cite the exact verified commit used in the submitted
version.

Maintained by [Diego Marques](https://github.com/DiegoMarquesMath).
