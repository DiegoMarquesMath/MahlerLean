# Cantor refinement of the local rigidity theorem

This note records the completed Lean 4 upgrade from the single-point fusion
theorem to the full Cantor-set conclusion of the current Theorem 1.1 of
*Arithmetic Rigidity of Analytic Functions and Mahler's Problem on Liouville Numbers*.

## Final statement

For every nonempty open set $V$ inside the analytic domain of a nonrational
real-analytic function $f$, the formalization constructs a set $K\subseteq V$
and an integer $b_0\ge2$ such that:

1. $K$ is nonempty;
2. $K$ is compact;
3. $K$ is perfect;
4. $K$ is totally disconnected;
5. every $\xi\in K$ is Liouville;
6. one common cutoff $b_0$ satisfies

   $$
   \left|f(\xi)-\frac{a}{b}\right|>b^{-100}
   $$

   for every $\xi\in K$, every $a\in\mathbb Z$, and every $b\ge b_0$;
7. consequently,

   $$
   \mu(f(\xi))\le100 \qquad (\xi\in K).
   $$

The theorem-level declaration is `MahlerLean.current_theorem_1_1`.

## Formalization structure

### C1 — Binary successor

Implemented in `MahlerLean/CantorFusion.lean`.

From each admissible fusion stage, the construction chooses a safe rational
center and produces two strictly separated successor intervals. Both children
inherit the source approximation, target avoidance, cutoff growth, denominator
growth, Wronskian-zero avoidance, and the next-stage tail estimate.

Principal declaration:

`MahlerLean.exists_binary_fusion_transition`.

### C2 — Binary recursion and compact levels

Implemented in `MahlerLean/CantorTree.lean`.

Nodes at depth $n$ are indexed by Boolean $n$-tuples. The file defines the
stage attached to each node, the compact level set, and the global limit set

$$
K=\bigcap_{n\ge0} E_n.
$$

It proves nestedness, compactness, nonemptiness, separation of distinct nodes,
and containment in the initial interval.

### C3 — Arithmetic along branches

Implemented in `MahlerLean/CantorBranches.lean`.

Every point of $K$ determines a unique coherent branch. The existing
single-branch fusion interface can therefore be reused verbatim along that
branch.

Principal declarations:

- `MahlerLean.cantorLimitSet_liouville`;
- `MahlerLean.cantorLimitSet_target_avoidance`;
- `MahlerLean.cantorLimitSet_irrationalityExponent_le`.

The target-avoidance theorem uses the root cutoff, so the same $b_0$ works for
all points of $K$.

### C4 — Nonempty subtrees

Implemented in `MahlerLean/CantorSubtree.lean`.

Following left children below any prescribed node gives a nested sequence of
nonempty compact intervals. Cantor intersection yields a point of the global
limit set inside every node interval.

Principal declaration:

`MahlerLean.cantorLimitSet_meets_node`.

### C5 — Shrinking diameters and perfectness

Implemented in `MahlerLean/CantorTopology.lean`.

Uniform source approximation gives a geometric upper bound for the width of
every level-$n$ interval. Hence level diameters tend uniformly to zero.

To prove perfectness, fix $x\in K$ and a neighborhood of $x$. At a sufficiently
deep level, the parent interval of $x$ lies inside the neighborhood. Switching
to the sibling child and using subtree nonemptiness produces a distinct point
of $K$ in the same neighborhood.

Principal declarations:

- `MahlerLean.cantorStage_width_lt_two_pow`;
- `MahlerLean.exists_cantorStage_width_lt`;
- `MahlerLean.cantorLimitSet_perfect`.

### C6 — Total disconnectedness

Implemented in `MahlerLean/CantorTopology.lean`.

For $x<y$ in $K$, take a level whose node widths are smaller than $y-x$.
The points must then lie in distinct node intervals. The endpoint of the node
containing $x$ lies strictly between $x$ and $y$, while endpoint-exclusion
shows that this point is not in $K$. The order characterization
`isTotallyDisconnected_iff_lt` then gives total disconnectedness.

Principal declarations:

- `MahlerLean.cantorStage_left_not_mem_limitSet`;
- `MahlerLean.cantorStage_right_not_mem_limitSet`;
- `MahlerLean.cantorLimitSet_isTotallyDisconnected`.

### C7 — Final analytic assembly

Implemented in `MahlerLean/CurrentTheoremOne.lean`.

The file combines:

- derivative localization;
- Proposition 5.1;
- Wronskian nonvanishing from analytic nonrationality;
- the binary fusion construction;
- the completed Cantor topology;
- the Liouville and target-avoidance conclusions.

It exposes the current manuscript numbering through:

- `MahlerLean.current_theorem_1_1`;
- `MahlerLean.current_corollary_1_2`;
- `MahlerLean.current_theorem_1_3`.

## Verification

The complete project build, warning-as-error source checks, and the listed
theorem audit pass on Lean 4.24.0 and mathlib v4.24.0.

Verified proof commit:

`dcbac6a16e910c22155e4882a3b11b2bb0c66222`.

The new Cantor declarations and the current theorem aliases are included in
`scripts/Audit.lean`.
