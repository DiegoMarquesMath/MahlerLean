# Cantor refinement of the local rigidity theorem

This note tracks the Lean 4 upgrade from the already verified single-point
fusion theorem to the full Cantor-set statement in the current Theorem 1.1
of the manuscript.

## Target statement

For every nonempty open interval `V` inside the analytic domain of a
nonrational real-analytic function `f`, construct a set `K ⊆ V` such that:

1. `K.Nonempty`;
2. `IsCompact K`;
3. `Perfect K`;
4. `IsTotallyDisconnected K`;
5. every `ξ ∈ K` is Liouville;
6. there is one integer cutoff `b₀ ≥ 2` such that, for every `ξ ∈ K`,
   every `a : ℤ`, and every `b ≥ b₀`,
   `b^(-100) < |f ξ - a / b|`;
7. consequently `irrationalityExponent (f ξ) ≤ 100` for every `ξ ∈ K`.

Items 1--4 are the topological Cantor-set package used by the manuscript.

## Formalization plan

### Step C1 — binary successor

Starting from one `FusionStage`, choose the same kind of safe rational
center as in the single-branch construction, but strengthen the scale budget
by a fixed constant factor.  Delete the next finite Wronskian-zero set and
the center, obtain one admissible interval, and take its left and right
thirds.

Both children inherit:

- strict nesting in the parent;
- avoidance of the next Wronskian-zero set;
- source approximation by the common center;
- target avoidance on the common denominator block;
- the tail estimate required at the next stage.

The children are strictly separated by the middle third.

Implementation: `MahlerLean/CantorFusion.lean`.

### Step C2 — binary recursion

Index level-`n` nodes by `Fin n → Bool`.  Recursively attach the two
children supplied by Step C1 to each node.  Prove:

- every child lies in the interior of its parent;
- siblings are strictly separated;
- denominator growth holds along every edge;
- cutoff growth holds along every edge;
- level intervals are pairwise disjoint;
- all level intervals satisfy a uniform diameter bound tending to zero.

### Step C3 — level sets and the Cantor set

Define

```
E n = ⋃ ω : Fin n → Bool, Icc (left n ω) (right n ω)
K   = ⋂ n, E n.
```

Because `Fin n → Bool` is finite, each `E n` is compact.  The level sets
are nonempty and nested, hence `K` is nonempty and compact.

### Step C4 — branch arithmetic

For `ξ ∈ K`, the pairwise-disjoint level intervals determine a unique node
at every depth and therefore a unique coherent branch.  Along this branch:

- the source denominators tend to infinity;
- the source approximation exponents are `n + 3`, hence `ξ` is
  Liouville;
- the successive target blocks cover every denominator above the common
  root cutoff;
- target avoidance gives one cutoff valid for every point of `K`.

### Step C5 — perfectness

Given `ξ ∈ K` and a neighborhood of `ξ`, go sufficiently deep that the
containing level interval lies inside the neighborhood.  Follow the sibling
child at the next split and then continue down that subtree.  Compact
intersection gives another point of `K` in the neighborhood, while sibling
separation makes it different from `ξ`.

This proves `Perfect K`.

### Step C6 — total disconnectedness

Use the order characterization available in mathlib:

```
isTotallyDisconnected_iff_lt
```

For two points `x < y` in `K`, choose a level whose interval diameters
are smaller than `y - x`.  The points must then lie in different
level intervals.  Their recursive sibling separation supplies a point
strictly between them that is outside the level set, hence outside `K`.

### Step C7 — final theorem and audit

Upgrade the current single-point theorem to the full current Theorem 1.1,
then derive Corollary 1.2 and Theorem 1.3 from it.  Add the final declarations
to `scripts/Audit.lean`, update the README status to verified, and record
the exact passing commit for the manuscript.
