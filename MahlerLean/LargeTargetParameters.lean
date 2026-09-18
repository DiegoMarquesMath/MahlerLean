import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic
import MahlerLean.FusionFromWronskians

/-!
Exact parameter inequalities for the large-target range in Proposition 5.1.

For a target block B = Q^u with u >= 1/5, the manuscript sets
d = ceil(10u), N = 2(d+1), kappa = 3(d+u)/(N-1), and
s = min(100u,A).  This file isolates the numerical estimates (5.24)--(5.29)
from the later determinant and sublevel arguments.
-/

noncomputable section
namespace MahlerLean

/-- The source degree d = ceil(10u) used in the large-target range. -/
def largeTargetDegree (u : ℝ) : ℕ := ⌈10 * u⌉₊

/-- The number N = 2(d+1) of target-linear monomials. -/
def largeTargetN (u : ℝ) : ℕ := 2 * (largeTargetDegree u + 1)

/-- The real number N, written without a cast through the natural expression. -/
def largeTargetNReal (u : ℝ) : ℝ := 2 * (largeTargetDegree u : ℝ) + 2

/-- The denominator N-1 = 2d+1 occurring in kappa and in the sublevel exponent. -/
def largeTargetDen (u : ℝ) : ℝ := 2 * (largeTargetDegree u : ℝ) + 1

/-- The short-cell exponent kappa = 3(d+u)/(N-1). -/
def largeTargetKappa (u : ℝ) : ℝ :=
  3 * ((largeTargetDegree u : ℝ) + u) / largeTargetDen u

/-- The perturbation exponent s = min(100u,A). -/
def largeTargetS (A : ℕ) (u : ℝ) : ℝ := min (100 * u) (A : ℝ)

theorem largeTargetDegree_lower (u : ℝ) :
    10 * u ≤ (largeTargetDegree u : ℝ) := by
  simpa [largeTargetDegree] using (Nat.le_ceil (10 * u))

theorem largeTargetDegree_upper (u : ℝ) (hu : (1 : ℝ) / 5 ≤ u) :
    (largeTargetDegree u : ℝ) ≤ 15 * u := by
  have hu0 : 0 ≤ 10 * u := by linarith
  have hlt : (largeTargetDegree u : ℝ) < 10 * u + 1 := by
    simpa [largeTargetDegree] using (Nat.ceil_lt_add_one hu0)
  linarith

theorem largeTargetDegree_ge_two (u : ℝ) (hu : (1 : ℝ) / 5 ≤ u) :
    2 ≤ largeTargetDegree u := by
  have h : (2 : ℝ) ≤ (largeTargetDegree u : ℝ) := by
    have hlo := largeTargetDegree_lower u
    linarith
  exact_mod_cast h

theorem largeTargetDegree_add_u_le (u : ℝ) (hu : (1 : ℝ) / 5 ≤ u) :
    (largeTargetDegree u : ℝ) + u ≤ 16 * u := by
  linarith [largeTargetDegree_upper u hu]

/-- The adaptive degree belongs to the finite degree range assumed in Proposition 5.1. -/
theorem largeTargetDegree_le_wronskianCutoff (A : ℕ) (u : ℝ)
    (huA : u < (A : ℝ) / 97) :
    largeTargetDegree u ≤ wronskianDegreeCutoff A := by
  unfold largeTargetDegree wronskianDegreeCutoff
  apply (Nat.ceil_mono ?_).trans (le_max_right _ _)
  nlinarith

theorem largeTargetN_cast (u : ℝ) :
    (largeTargetN u : ℝ) = largeTargetNReal u := by
  simp [largeTargetN, largeTargetNReal]
  ring

theorem largeTargetDen_eq_N_minus_one (u : ℝ) :
    largeTargetDen u = largeTargetNReal u - 1 := by
  simp [largeTargetDen, largeTargetNReal]
  ring

theorem largeTargetDen_pos (u : ℝ) : 0 < largeTargetDen u := by
  unfold largeTargetDen
  have hd : 0 ≤ (largeTargetDegree u : ℝ) := by positivity
  linarith

theorem largeTargetDen_le_35u (u : ℝ) (hu : (1 : ℝ) / 5 ≤ u) :
    largeTargetDen u ≤ 35 * u := by
  unfold largeTargetDen
  have hd := largeTargetDegree_upper u hu
  linarith

/-- The cell exponent bound kappa <= 33/20 in (5.25). -/
theorem largeTargetKappa_le (u : ℝ) :
    largeTargetKappa u ≤ (33 : ℝ) / 20 := by
  rw [largeTargetKappa, div_le_iff₀ (largeTargetDen_pos u)]
  unfold largeTargetDen
  have hlo := largeTargetDegree_lower u
  nlinarith

theorem largeTargetN_ratio_nonneg (u : ℝ) :
    0 ≤ largeTargetNReal u / largeTargetDen u := by
  exact div_nonneg (by unfold largeTargetNReal; positivity) (largeTargetDen_pos u).le

theorem largeTargetN_ratio_le_two (u : ℝ) :
    largeTargetNReal u / largeTargetDen u ≤ 2 := by
  rw [div_le_iff₀ (largeTargetDen_pos u)]
  unfold largeTargetNReal largeTargetDen
  have hd : 0 ≤ (largeTargetDegree u : ℝ) := by positivity
  nlinarith

/-- The estimate kappa*N <= 96u used in (5.27). -/
theorem largeTargetKappa_mul_N_le_96u (u : ℝ) (hu : (1 : ℝ) / 5 ≤ u) :
    largeTargetKappa u * largeTargetNReal u ≤ 96 * u := by
  have hu0 : 0 ≤ u := by linarith
  have hdu := largeTargetDegree_add_u_le u hu
  have hnum : 3 * ((largeTargetDegree u : ℝ) + u) ≤ 48 * u := by
    linarith
  have hratio0 := largeTargetN_ratio_nonneg u
  have hratio2 := largeTargetN_ratio_le_two u
  calc
    largeTargetKappa u * largeTargetNReal u =
        (3 * ((largeTargetDegree u : ℝ) + u)) *
          (largeTargetNReal u / largeTargetDen u) := by
            rw [largeTargetKappa]
            ring
    _ ≤ (48 * u) * (largeTargetNReal u / largeTargetDen u) :=
      mul_le_mul_of_nonneg_right hnum hratio0
    _ ≤ (48 * u) * 2 :=
      mul_le_mul_of_nonneg_left hratio2 (by positivity)
    _ = 96 * u := by ring

/-- The lower bound s >= 97u from the upper target cutoff B < Q^(A/97). -/
theorem largeTargetS_ge_97u (A : ℕ) (u : ℝ) (hu : (1 : ℝ) / 5 ≤ u)
    (huA : 97 * u < (A : ℝ)) :
    97 * u ≤ largeTargetS A u := by
  unfold largeTargetS
  apply le_min
  · nlinarith
  · exact huA.le

/-- The perturbation gap s-kappa*N >= u, hence at least 1/5. -/
theorem largeTargetPerturbationGap (A : ℕ) (u : ℝ)
    (hu : (1 : ℝ) / 5 ≤ u) (huA : 97 * u < (A : ℝ)) :
    u ≤ largeTargetS A u - largeTargetKappa u * largeTargetNReal u := by
  have hs := largeTargetS_ge_97u A u hu huA
  have hk := largeTargetKappa_mul_N_le_96u u hu
  linarith

theorem largeTargetPerturbationGap_one_fifth (A : ℕ) (u : ℝ)
    (hu : (1 : ℝ) / 5 ≤ u) (huA : 97 * u < (A : ℝ)) :
    (1 : ℝ) / 5 ≤ largeTargetS A u - largeTargetKappa u * largeTargetNReal u :=
  hu.trans (largeTargetPerturbationGap A u hu huA)

/-- The Farey/sublevel exponent s/(N-1) >= 97/35 in (5.29). -/
theorem largeTargetFareyExponent (A : ℕ) (u : ℝ)
    (hu : (1 : ℝ) / 5 ≤ u) (huA : 97 * u < (A : ℝ)) :
    (97 : ℝ) / 35 ≤ largeTargetS A u / largeTargetDen u := by
  rw [le_div_iff₀ (largeTargetDen_pos u)]
  have hs := largeTargetS_ge_97u A u hu huA
  have hden := largeTargetDen_le_35u u hu
  nlinarith

theorem largeTargetFareyExponent_gt_two (A : ℕ) (u : ℝ)
    (hu : (1 : ℝ) / 5 ≤ u) (huA : 97 * u < (A : ℝ)) :
    2 < largeTargetS A u / largeTargetDen u := by
  have hc : (2 : ℝ) < 97 / 35 := by norm_num
  exact hc.trans_le (largeTargetFareyExponent A u hu huA)

/-- The three numerical inequalities driving the large-target argument,
together with membership of the adaptive degree in the permitted range. -/
theorem largeTargetParameterBundle (A : ℕ) (u : ℝ)
    (hu : (1 : ℝ) / 5 ≤ u) (huCutoff : u < (A : ℝ) / 97) :
    2 ≤ largeTargetDegree u ∧
    largeTargetDegree u ≤ wronskianDegreeCutoff A ∧
    largeTargetKappa u ≤ (33 : ℝ) / 20 ∧
    (1 : ℝ) / 5 ≤ largeTargetS A u - largeTargetKappa u * largeTargetNReal u ∧
    2 < largeTargetS A u / largeTargetDen u := by
  have huA : 97 * u < (A : ℝ) := by nlinarith
  exact ⟨largeTargetDegree_ge_two u hu,
    largeTargetDegree_le_wronskianCutoff A u huCutoff,
    largeTargetKappa_le u,
    largeTargetPerturbationGap_one_fifth A u hu huA,
    largeTargetFareyExponent_gt_two A u hu huA⟩

end MahlerLean
