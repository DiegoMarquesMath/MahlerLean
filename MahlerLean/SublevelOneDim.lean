import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Card
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Order.Fin.Basic
import MahlerLean.UniformJet
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Order.IntermediateValue

/-!
One-dimensional sublevel estimates: Rolle-theoretic infrastructure.

This module begins the formalization of Lemma 3.4.  The first steps are
the Rolle mechanisms that propagate repeated zeros to zeros of higher
iterated derivatives.
-/

noncomputable section
namespace MahlerLean

/-- Rolle's theorem expressed directly for consecutive iterated derivatives. -/
theorem exists_iteratedDeriv_succ_eq_zero
    {g : ℝ → ℝ} {n : ℕ} {a b : ℝ}
    (hab : a < b)
    (hcont : ContinuousOn (iteratedDeriv n g) (Set.Icc a b))
    (heq : iteratedDeriv n g a = iteratedDeriv n g b) :
    ∃ c ∈ Set.Ioo a b, iteratedDeriv (n + 1) g c = 0 := by
  obtain ⟨c, hc, hzero⟩ := exists_deriv_eq_zero hab hcont heq
  refine ⟨c, hc, ?_⟩
  rw [iteratedDeriv_succ]
  exact hzero

/-- Two zeros of the nth derivative force a zero of the (n+1)st derivative
strictly between them. -/
theorem exists_iteratedDeriv_succ_eq_zero_of_endpoints
    {g : ℝ → ℝ} {n : ℕ} {a b : ℝ}
    (hab : a < b)
    (hcont : ContinuousOn (iteratedDeriv n g) (Set.Icc a b))
    (ha : iteratedDeriv n g a = 0)
    (hb : iteratedDeriv n g b = 0) :
    ∃ c ∈ Set.Ioo a b, iteratedDeriv (n + 1) g c = 0 := by
  exact exists_iteratedDeriv_succ_eq_zero hab hcont (ha.trans hb.symm)

/-- A positive absolute lower bound excludes zeros. -/
theorem iteratedDeriv_ne_zero_of_abs_lower_bound
    {g : ℝ → ℝ} {n : ℕ} {a b lam : ℝ}
    (hlam : 0 < lam)
    (hlow : ∀ x ∈ Set.Icc a b, lam ≤ |iteratedDeriv n g x|) :
    ∀ x ∈ Set.Icc a b, iteratedDeriv n g x ≠ 0 := by
  intro x hx hzero
  have h := hlow x hx
  rw [hzero, abs_zero] at h
  linarith

/-- Rolle interlacing: between consecutive ordered zeros of a continuous
function one can choose ordered zeros of its derivative. -/
theorem exists_interlaced_deriv_zeros
    {g : ℝ → ℝ} {m : ℕ} {a b : ℝ}
    (x : Fin (m + 1) → ℝ)
    (hxmono : StrictMono x)
    (hxmem : ∀ i, x i ∈ Set.Icc a b)
    (hcont : ContinuousOn g (Set.Icc a b))
    (hz : ∀ i, g (x i) = 0) :
    ∃ y : Fin m → ℝ,
      StrictMono y ∧
      (∀ i : Fin m, x i.castSucc < y i ∧ y i < x i.succ) ∧
      ∀ i : Fin m, deriv g (y i) = 0 := by
  classical

  have hrolle :
      ∀ i : Fin m,
        ∃ c ∈ Set.Ioo (x i.castSucc) (x i.succ), deriv g c = 0 := by
    intro i

    have hlt : x i.castSucc < x i.succ := by
      exact hxmono (Fin.castSucc_lt_succ i)

    have hcont' :
        ContinuousOn g (Set.Icc (x i.castSucc) (x i.succ)) := by
      apply hcont.mono
      intro z hzmem
      constructor
      · exact (hxmem i.castSucc).1.trans hzmem.1
      · exact hzmem.2.trans (hxmem i.succ).2

    exact exists_deriv_eq_zero hlt hcont'
      ((hz i.castSucc).trans (hz i.succ).symm)

  choose y hyI hyzero using hrolle

  have hymono : StrictMono y := by
    intro i j hij

    have hidx : i.succ ≤ j.castSucc := by
      change i.val + 1 ≤ j.val
      exact Nat.succ_le_of_lt (show i.val < j.val from hij)

    have hxle : x i.succ ≤ x j.castSucc :=
      hxmono.monotone hidx

    have hi : y i < x i.succ := (hyI i).2
    have hj : x j.castSucc < y j := (hyI j).1

    linarith

  exact ⟨y, hymono, fun i => hyI i, hyzero⟩

/-- The same interlacing statement for two consecutive iterated derivatives. -/
theorem exists_interlaced_iteratedDeriv_zeros
    {g : ℝ → ℝ} {n m : ℕ} {a b : ℝ}
    (x : Fin (m + 1) → ℝ)
    (hxmono : StrictMono x)
    (hxmem : ∀ i, x i ∈ Set.Icc a b)
    (hcont : ContinuousOn (iteratedDeriv n g) (Set.Icc a b))
    (hz : ∀ i, iteratedDeriv n g (x i) = 0) :
    ∃ y : Fin m → ℝ,
      StrictMono y ∧
      (∀ i : Fin m, x i.castSucc < y i ∧ y i < x i.succ) ∧
      ∀ i : Fin m, iteratedDeriv (n + 1) g (y i) = 0 := by
  obtain ⟨y, hymono, hybetween, hyzero⟩ :=
    exists_interlaced_deriv_zeros
      (g := iteratedDeriv n g) x hxmono hxmem hcont hz

  refine ⟨y, hymono, hybetween, ?_⟩
  intro i
  rw [iteratedDeriv_succ]
  exact hyzero i


/-- Iterated Rolle theorem with an offset derivative order.

If `k+1` ordered points are zeros of the `n`th iterated derivative, then
the `(n+k)`th iterated derivative has a zero between the extreme points.
The global continuity hypothesis is tailored to the analytic application
in the proof of Theorem 1.2. -/
theorem exists_iteratedDeriv_add_eq_zero_of_many_zeros
    {g : ℝ → ℝ} {a b : ℝ}
    (hcont : ∀ r : ℕ,
      ContinuousOn (iteratedDeriv r g) (Set.Icc a b)) :
    ∀ (n k : ℕ) (x : Fin (k + 1) → ℝ),
      StrictMono x →
      (∀ i, x i ∈ Set.Icc a b) →
      (∀ i, iteratedDeriv n g (x i) = 0) →
      ∃ c ∈ Set.Icc a b, iteratedDeriv (n + k) g c = 0 := by
  intro n k
  induction k generalizing n with
  | zero =>
      intro x _hxmono hxmem hz
      refine ⟨x 0, hxmem 0, ?_⟩
      simpa using hz 0

  | succ k ih =>
      intro x hxmono hxmem hz

      obtain ⟨y, hymono, hybetween, hyzero⟩ :=
        exists_interlaced_iteratedDeriv_zeros
          (g := g) (n := n) x hxmono hxmem (hcont n) hz

      have hymem : ∀ i, y i ∈ Set.Icc a b := by
        intro i
        constructor
        · exact (hxmem i.castSucc).1.trans (hybetween i).1.le
        · exact (hybetween i).2.le.trans (hxmem i.succ).2

      obtain ⟨c, hc, hczero⟩ :=
        ih (n + 1) y hymono hymem hyzero

      refine ⟨c, hc, ?_⟩
      simpa [Nat.add_assoc, Nat.one_add] using hczero

/-- Iterated Rolle starting from zeros of the original function. -/
theorem exists_iteratedDeriv_eq_zero_of_many_zeros
    {g : ℝ → ℝ} {k : ℕ} {a b : ℝ}
    (hcont : ∀ r : ℕ,
      ContinuousOn (iteratedDeriv r g) (Set.Icc a b))
    (x : Fin (k + 1) → ℝ)
    (hxmono : StrictMono x)
    (hxmem : ∀ i, x i ∈ Set.Icc a b)
    (hz : ∀ i, g (x i) = 0) :
    ∃ c ∈ Set.Icc a b, iteratedDeriv k g c = 0 := by
  have hz0 : ∀ i, iteratedDeriv 0 g (x i) = 0 := by
    intro i
    simpa using hz i

  simpa using
    exists_iteratedDeriv_add_eq_zero_of_many_zeros
      (g := g) (a := a) (b := b) hcont 0 k x hxmono hxmem hz0

/-- If the kth derivative has no zero on the interval, the function
cannot have `k+1` strictly ordered zeros there. -/
theorem not_exists_many_zeros_of_iteratedDeriv_ne_zero
    {g : ℝ → ℝ} {k : ℕ} {a b : ℝ}
    (hcont : ∀ r : ℕ,
      ContinuousOn (iteratedDeriv r g) (Set.Icc a b))
    (hnozero :
      ∀ c ∈ Set.Icc a b, iteratedDeriv k g c ≠ 0) :
    ¬ ∃ x : Fin (k + 1) → ℝ,
        StrictMono x ∧
        (∀ i, x i ∈ Set.Icc a b) ∧
        ∀ i, g (x i) = 0 := by
  rintro ⟨x, hxmono, hxmem, hz⟩

  obtain ⟨c, hc, hczero⟩ :=
    exists_iteratedDeriv_eq_zero_of_many_zeros
      hcont x hxmono hxmem hz

  exact hnozero c hc hczero

/-- A positive lower bound for the absolute kth derivative rules out
`k+1` strictly ordered zeros. -/
theorem not_exists_many_zeros_of_iteratedDeriv_abs_lower_bound
    {g : ℝ → ℝ} {k : ℕ} {a b lam : ℝ}
    (hcont : ∀ r : ℕ,
      ContinuousOn (iteratedDeriv r g) (Set.Icc a b))
    (hlam : 0 < lam)
    (hlow :
      ∀ c ∈ Set.Icc a b, lam ≤ |iteratedDeriv k g c|) :
    ¬ ∃ x : Fin (k + 1) → ℝ,
        StrictMono x ∧
        (∀ i, x i ∈ Set.Icc a b) ∧
        ∀ i, g (x i) = 0 := by
  apply not_exists_many_zeros_of_iteratedDeriv_ne_zero hcont
  exact iteratedDeriv_ne_zero_of_abs_lower_bound hlam hlow


/-- Adding a constant does not change any positive-order iterated derivative,
so the same Rolle argument controls arbitrary level sets `g = t`. -/
theorem not_exists_many_level_hits_of_iteratedDeriv_ne_zero
    {g : ℝ → ℝ} {k : ℕ} {a b t : ℝ}
    (hk : 0 < k)
    (hcont : ∀ r : ℕ,
      ContinuousOn (iteratedDeriv r g) (Set.Icc a b))
    (hnozero :
      ∀ c ∈ Set.Icc a b, iteratedDeriv k g c ≠ 0) :
    ¬ ∃ x : Fin (k + 1) → ℝ,
        StrictMono x ∧
        (∀ i, x i ∈ Set.Icc a b) ∧
        ∀ i, g (x i) = t := by

  let h : ℝ → ℝ := fun z => -t + g z

  have hcont_h :
      ∀ r : ℕ,
        ContinuousOn (iteratedDeriv r h) (Set.Icc a b) := by
    intro r
    by_cases hr : r = 0
    · subst r
      have hg : ContinuousOn g (Set.Icc a b) := by
        simpa using hcont 0
      simpa [h] using
        (continuousOn_const.add hg :
          ContinuousOn (fun z : ℝ => -t + g z) (Set.Icc a b))
    · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
      have heq :
          iteratedDeriv r h = iteratedDeriv r g := by
        funext z
        simpa [h] using
          (iteratedDeriv_const_add
            (f := g) (x := z) hrpos (-t))
      rw [heq]
      exact hcont r

  have hnozero_h :
      ∀ c ∈ Set.Icc a b, iteratedDeriv k h c ≠ 0 := by
    intro c hc
    have heq :
        iteratedDeriv k h c = iteratedDeriv k g c := by
      simpa [h] using
        (iteratedDeriv_const_add
          (f := g) (x := c) hk (-t))
    rw [heq]
    exact hnozero c hc

  rintro ⟨x, hxmono, hxmem, hxlevel⟩
  apply (not_exists_many_zeros_of_iteratedDeriv_ne_zero hcont_h hnozero_h)
  refine ⟨x, hxmono, hxmem, ?_⟩
  intro i
  simp [h, hxlevel i]

/-- A positive absolute lower bound for the kth derivative therefore
rules out `k+1` strictly ordered hits of any fixed level. -/
theorem not_exists_many_level_hits_of_iteratedDeriv_abs_lower_bound
    {g : ℝ → ℝ} {k : ℕ} {a b t lam : ℝ}
    (hk : 0 < k)
    (hcont : ∀ r : ℕ,
      ContinuousOn (iteratedDeriv r g) (Set.Icc a b))
    (hlam : 0 < lam)
    (hlow :
      ∀ c ∈ Set.Icc a b, lam ≤ |iteratedDeriv k g c|) :
    ¬ ∃ x : Fin (k + 1) → ℝ,
        StrictMono x ∧
        (∀ i, x i ∈ Set.Icc a b) ∧
        ∀ i, g (x i) = t := by
  apply not_exists_many_level_hits_of_iteratedDeriv_ne_zero hk hcont
  exact iteratedDeriv_ne_zero_of_abs_lower_bound hlam hlow


/-- If a function is bounded by `eps` at `k+1` equally spaced points,
then its kth forward difference is bounded by `2^k * eps`. -/
theorem norm_fwdDiff_iter_le_two_pow_mul
    (k : ℕ) {g : ℝ → ℝ} {u h eps : ℝ}
    (heps : 0 ≤ eps)
    (hbound :
      ∀ j ∈ Finset.range (k + 1),
        ‖g (u + (j : ℝ) * h)‖ ≤ eps) :
    ‖(fwdDiff h)^[k] g u‖ ≤ (2 : ℝ) ^ k * eps := by
  induction k generalizing g u eps with
  | zero =>
      simpa using hbound 0 (by simp)

  | succ k ih =>
      have hbound' :
          ∀ j ∈ Finset.range (k + 1),
            ‖fwdDiff h g (u + (j : ℝ) * h)‖ ≤ 2 * eps := by
        intro j hj

        have hj0 :
            j ∈ Finset.range (Nat.succ k + 1) := by
          apply Finset.mem_range.mpr
          have hjlt : j < k + 1 := Finset.mem_range.mp hj
          omega

        have hj1 :
            j + 1 ∈ Finset.range (Nat.succ k + 1) := by
          apply Finset.mem_range.mpr
          have hjlt : j < k + 1 := Finset.mem_range.mp hj
          omega

        have h0 := hbound j hj0
        have h1 := hbound (j + 1) hj1

        have hshift :
            u + (j : ℝ) * h + h =
              u + ((j + 1 : ℕ) : ℝ) * h := by
          push_cast
          ring

        rw [fwdDiff, hshift]

        calc
          ‖g (u + ((j + 1 : ℕ) : ℝ) * h) -
              g (u + (j : ℝ) * h)‖
              ≤ ‖g (u + ((j + 1 : ℕ) : ℝ) * h)‖ +
                ‖g (u + (j : ℝ) * h)‖ := norm_sub_le _ _
          _ ≤ eps + eps := add_le_add h1 h0
          _ = 2 * eps := by ring

      have hih :=
        ih (g := fwdDiff h g) (u := u) (eps := 2 * eps)
          (by positivity) hbound'

      rw [Function.iterate_succ_apply]
      simpa [pow_succ, mul_assoc] using hih


/-- Differentiation commutes with an iterated forward difference,
provided the original function has the required derivatives at all
shifted points. -/
theorem hasDerivAt_fwdDiff_iter
    (k : ℕ) {g g' : ℝ → ℝ} {x h : ℝ}
    (hderiv :
      ∀ j ∈ Finset.range (k + 1),
        HasDerivAt g
          (g' (x + (j : ℝ) * h))
          (x + (j : ℝ) * h)) :
    HasDerivAt ((fwdDiff h)^[k] g)
      (((fwdDiff h)^[k] g') x) x := by
  induction k generalizing x with
  | zero =>
      simpa using hderiv 0 (by simp)

  | succ k ih =>
      have hx :
          HasDerivAt ((fwdDiff h)^[k] g)
            (((fwdDiff h)^[k] g') x) x := by
        apply ih
        intro j hj
        apply hderiv j
        apply Finset.mem_range.mpr
        have hjlt := Finset.mem_range.mp hj
        omega

      have hxph :
          HasDerivAt ((fwdDiff h)^[k] g)
            (((fwdDiff h)^[k] g') (x + h)) (x + h) := by
        apply ih
        intro j hj

        have hj1 :
            j + 1 ∈ Finset.range (Nat.succ k + 1) := by
          apply Finset.mem_range.mpr
          have hjlt := Finset.mem_range.mp hj
          omega

        have hpt :
            x + h + (j : ℝ) * h =
              x + ((j + 1 : ℕ) : ℝ) * h := by
          push_cast
          ring

        rw [hpt]
        exact hderiv (j + 1) hj1

      have hshift :
          HasDerivAt
            (fun y => ((fwdDiff h)^[k] g) (y + h))
            (((fwdDiff h)^[k] g') (x + h)) x :=
        hxph.comp_add_const x h

      have hsub := hshift.sub hx

      simpa [Function.iterate_succ_apply', fwdDiff] using hsub


/-- Generalized mean-value theorem for equally spaced finite differences.

For a positive step `h`, the kth forward difference of the nth iterated
derivative equals `h^k` times the `(n+k)`th derivative at some point of
the interval spanned by the sample points. -/
theorem exists_fwdDiff_iter_eq_pow_mul_iteratedDeriv
    {g : ℝ → ℝ} {a b : ℝ}
    (hdiff :
      ∀ r : ℕ, ∀ z ∈ Set.Icc a b,
        DifferentiableAt ℝ (iteratedDeriv r g) z) :
    ∀ (n k : ℕ) (u h : ℝ),
      0 < h →
      Set.Icc u (u + (k : ℝ) * h) ⊆ Set.Icc a b →
      ∃ ξ ∈ Set.Icc u (u + (k : ℝ) * h),
        (fwdDiff h)^[k] (iteratedDeriv n g) u =
          h ^ k * iteratedDeriv (n + k) g ξ := by
  intro n k
  induction k generalizing n with
  | zero =>
      intro u h _hh _hseg
      refine ⟨u, ?_, ?_⟩
      · simp
      · simp

  | succ k ih =>
      intro u h hh hseg

      let F : ℝ → ℝ :=
        (fwdDiff h)^[k] (iteratedDeriv n g)

      let F' : ℝ → ℝ :=
        (fwdDiff h)^[k] (iteratedDeriv (n + 1) g)

      have hsmall :
          Set.Icc u (u + h) ⊆
            Set.Icc u (u + ((Nat.succ k : ℕ) : ℝ) * h) := by
        intro y hy
        constructor
        · exact hy.1
        · calc
            y ≤ u + h := hy.2
            _ ≤ u + h + (k : ℝ) * h := by
              have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
              have hkh0 : 0 ≤ (k : ℝ) * h :=
                mul_nonneg hk0 hh.le
              linarith
            _ = u + ((Nat.succ k : ℕ) : ℝ) * h := by
              push_cast
              ring

      have hFderiv :
          ∀ y ∈ Set.Icc u (u + h),
            HasDerivAt F (F' y) y := by
        intro y hy

        have hpoints :
            ∀ j ∈ Finset.range (k + 1),
              HasDerivAt (iteratedDeriv n g)
                (iteratedDeriv (n + 1) g
                  (y + (j : ℝ) * h))
                (y + (j : ℝ) * h) := by
          intro j hj

          have hjnat : j ≤ k := by
            exact Nat.le_of_lt_succ (Finset.mem_range.mp hj)

          have hjreal : (j : ℝ) ≤ (k : ℝ) := by
            exact_mod_cast hjnat

          have hjnonneg : (0 : ℝ) ≤ (j : ℝ) * h := by
            positivity

          have hpoint :
              y + (j : ℝ) * h ∈
                Set.Icc u
                  (u + ((Nat.succ k : ℕ) : ℝ) * h) := by
            constructor
            · exact hy.1.trans (by linarith)
            · calc
                y + (j : ℝ) * h
                    ≤ (u + h) + (k : ℝ) * h := by
                      exact add_le_add hy.2
                        (mul_le_mul_of_nonneg_right hjreal hh.le)
                _ = u + ((Nat.succ k : ℕ) : ℝ) * h := by
                      push_cast
                      ring

          have hamb :
              y + (j : ℝ) * h ∈ Set.Icc a b :=
            hseg hpoint

          have hd :=
            (hdiff n (y + (j : ℝ) * h) hamb).hasDerivAt

          rw [iteratedDeriv_succ] at ⊢
          exact hd

        simpa [F, F'] using
          hasDerivAt_fwdDiff_iter
            k
            (g := iteratedDeriv n g)
            (g' := iteratedDeriv (n + 1) g)
            (x := y) (h := h) hpoints

      have hFcont :
          ContinuousOn F (Set.Icc u (u + h)) := by
        intro y hy
        exact (hFderiv y hy).continuousAt.continuousWithinAt

      have huh : u < u + h := by
        linarith

      obtain ⟨c, hc, hmean⟩ :=
        exists_hasDerivAt_eq_slope
          F F' huh hFcont
          (fun y hy =>
            hFderiv y ⟨hy.1.le, hy.2.le⟩)

      have hhne : h ≠ 0 := ne_of_gt hh

      have hdelta :
          F (u + h) - F u = h * F' c := by
        have hmean' :
            F' c = (F (u + h) - F u) / h := by
          convert hmean using 1; ring
        have hm :
            F' c * h = F (u + h) - F u :=
          (eq_div_iff hhne).mp hmean'
        calc
          F (u + h) - F u = F' c * h := hm.symm
          _ = h * F' c := by ring

      have hcseg :
          Set.Icc c (c + (k : ℝ) * h) ⊆ Set.Icc a b := by
        intro z hz

        have hparent :
            z ∈ Set.Icc u
              (u + ((Nat.succ k : ℕ) : ℝ) * h) := by
          constructor
          · exact hc.1.le.trans hz.1
          · calc
              z ≤ c + (k : ℝ) * h := hz.2
              _ ≤ (u + h) + (k : ℝ) * h := by
                    exact add_le_add_right hc.2.le ((k : ℝ) * h)
              _ = u + ((Nat.succ k : ℕ) : ℝ) * h := by
                    push_cast
                    ring

        exact hseg hparent

      obtain ⟨ξ, hξ, hih⟩ :=
        ih (n + 1) c h hh hcseg

      refine ⟨ξ, ?_, ?_⟩

      · constructor
        · exact hc.1.le.trans hξ.1
        · calc
            ξ ≤ c + (k : ℝ) * h := hξ.2
            _ ≤ (u + h) + (k : ℝ) * h := by
                  exact add_le_add_right hc.2.le ((k : ℝ) * h)
            _ = u + ((Nat.succ k : ℕ) : ℝ) * h := by
                  push_cast
                  ring

      · rw [Function.iterate_succ_apply', fwdDiff]
        change F (u + h) - F u =
          h ^ Nat.succ k *
            iteratedDeriv (n + Nat.succ k) g ξ

        rw [hdelta]

        have hih' :
            F' c =
              h ^ k * iteratedDeriv (n + 1 + k) g ξ := by
          simpa [F'] using hih

        have hindex :
            n + 1 + k = n + Nat.succ k := by
          omega

        rw [hih', hindex, pow_succ]
        ring


/-- Quantitative core of the one-dimensional sublevel estimate.

If `|g| ≤ eps` throughout `[u,v]` and the absolute value of the kth
derivative is at least `lam`, then the normalized interval length
satisfies the expected kth-power bound. -/
theorem sublevel_interval_power_bound
    {g : ℝ → ℝ} {k : ℕ} {a b u v eps lam : ℝ}
    (hk : 0 < k)
    (huv : u < v)
    (hdiff :
      ∀ r : ℕ, ∀ z ∈ Set.Icc a b,
        DifferentiableAt ℝ (iteratedDeriv r g) z)
    (hseg : Set.Icc u v ⊆ Set.Icc a b)
    (heps : 0 ≤ eps)
    (hbound : ∀ x ∈ Set.Icc u v, ‖g x‖ ≤ eps)
    (hlow :
      ∀ x ∈ Set.Icc u v,
        lam ≤ |iteratedDeriv k g x|) :
    lam * ((v - u) / (k : ℝ)) ^ k
      ≤ (2 : ℝ) ^ k * eps := by

  have hkR : (0 : ℝ) < (k : ℝ) := by
    exact_mod_cast hk

  have hkRne : (k : ℝ) ≠ 0 := ne_of_gt hkR

  let h : ℝ := (v - u) / (k : ℝ)

  have hh : 0 < h := by
    dsimp [h]
    exact div_pos (sub_pos.mpr huv) hkR

  have hkend :
      u + (k : ℝ) * h = v := by
    dsimp [h]
    field_simp [hkRne]
    ring

  have hsample :
      ∀ j ∈ Finset.range (k + 1),
        u + (j : ℝ) * h ∈ Set.Icc u v := by
    intro j hj

    have hjle : j ≤ k := by
      exact Nat.le_of_lt_succ (Finset.mem_range.mp hj)

    have hjR : (j : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast hjle

    constructor
    · have hjnonneg : 0 ≤ (j : ℝ) * h := by
        exact mul_nonneg (Nat.cast_nonneg j) hh.le
      linarith

    · rw [← hkend]
      exact add_le_add_left
        (mul_le_mul_of_nonneg_right hjR hh.le) u

  have hfdUpper :
      ‖(fwdDiff h)^[k] g u‖
        ≤ (2 : ℝ) ^ k * eps := by
    apply norm_fwdDiff_iter_le_two_pow_mul k heps
    intro j hj
    exact hbound _ (hsample j hj)

  have hseg' :
      Set.Icc u (u + (k : ℝ) * h) ⊆
        Set.Icc a b := by
    intro x hx
    apply hseg
    simpa [hkend] using hx

  obtain ⟨ξ, hξ, hfdEq⟩ :=
    exists_fwdDiff_iter_eq_pow_mul_iteratedDeriv
      (g := g) (a := a) (b := b)
      hdiff 0 k u h hh hseg'

  have hξuv : ξ ∈ Set.Icc u v := by
    simpa [hkend] using hξ

  have hfdEq' :
      (fwdDiff h)^[k] g u =
        h ^ k * iteratedDeriv k g ξ := by
    simpa using hfdEq

  have hpow_nonneg : 0 ≤ h ^ k :=
    pow_nonneg hh.le k

  have hfdAbs :
      |(fwdDiff h)^[k] g u| =
        h ^ k * |iteratedDeriv k g ξ| := by
    rw [hfdEq', abs_mul, abs_of_nonneg hpow_nonneg]

  have hfdLower :
      lam * h ^ k ≤
        |(fwdDiff h)^[k] g u| := by
    calc
      lam * h ^ k = h ^ k * lam := by ring
      _ ≤ h ^ k * |iteratedDeriv k g ξ| :=
        mul_le_mul_of_nonneg_left (hlow ξ hξuv) hpow_nonneg
      _ = |(fwdDiff h)^[k] g u| := hfdAbs.symm

  have hfdUpper' :
      |(fwdDiff h)^[k] g u|
        ≤ (2 : ℝ) ^ k * eps := by
    simpa [Real.norm_eq_abs] using hfdUpper

  have hfinal :
      lam * h ^ k ≤ (2 : ℝ) ^ k * eps :=
    hfdLower.trans hfdUpper'

  simpa [h] using hfinal


/-- Length form of the quantitative one-dimensional sublevel bound.

If `|g| ≤ eps` throughout `[u,v]` and `|g^(k)| ≥ lam > 0`,
then the interval has length at most
`2 k (eps / lam)^(1/k)`. -/
theorem sublevel_interval_length_bound
    {g : ℝ → ℝ} {k : ℕ} {a b u v eps lam : ℝ}
    (hk : 0 < k)
    (huv : u < v)
    (hdiff :
      ∀ r : ℕ, ∀ z ∈ Set.Icc a b,
        DifferentiableAt ℝ (iteratedDeriv r g) z)
    (hseg : Set.Icc u v ⊆ Set.Icc a b)
    (heps : 0 ≤ eps)
    (hlam : 0 < lam)
    (hbound : ∀ x ∈ Set.Icc u v, ‖g x‖ ≤ eps)
    (hlow :
      ∀ x ∈ Set.Icc u v,
        lam ≤ |iteratedDeriv k g x|) :
    v - u ≤
      2 * (k : ℝ) *
        (eps / lam) ^ ((k : ℝ)⁻¹) := by

  have hkne : k ≠ 0 :=
    Nat.ne_of_gt hk

  have hkR : (0 : ℝ) < (k : ℝ) := by
    exact_mod_cast hk

  have hxnonneg :
      0 ≤ (v - u) / (k : ℝ) := by
    exact div_nonneg (sub_nonneg.mpr huv.le) hkR.le

  have hq :
      0 ≤ eps / lam := by
    exact div_nonneg heps hlam.le

  have hpower :=
    sublevel_interval_power_bound
      (g := g) (k := k)
      (a := a) (b := b) (u := u) (v := v)
      (eps := eps) (lam := lam)
      hk huv hdiff hseg heps hbound hlow

  have hpow :
      ((v - u) / (k : ℝ)) ^ k
        ≤ (2 : ℝ) ^ k * (eps / lam) := by
    calc
      ((v - u) / (k : ℝ)) ^ k
          ≤ ((2 : ℝ) ^ k * eps) / lam := by
              apply (le_div_iff₀ hlam).2
              simpa [mul_comm] using hpower
      _ = (2 : ℝ) ^ k * (eps / lam) := by
              ring

  let root : ℝ :=
    (eps / lam) ^ ((k : ℝ)⁻¹)

  have hroot_nonneg : 0 ≤ root := by
    dsimp [root]
    exact Real.rpow_nonneg hq _

  have hroot_pow :
      root ^ k = eps / lam := by
    dsimp [root]
    exact Real.rpow_inv_natCast_pow hq hkne

  have hRnonneg :
      0 ≤ 2 * root := by
    positivity

  have hRpow :
      (2 * root) ^ k =
        (2 : ℝ) ^ k * (eps / lam) := by
    rw [mul_pow, hroot_pow]

  have hxle :
      (v - u) / (k : ℝ) ≤ 2 * root := by
    apply
      (pow_le_pow_iff_left₀
        hxnonneg hRnonneg hkne).mp
    rw [hRpow]
    exact hpow

  have hmul :=
    mul_le_mul_of_nonneg_left hxle hkR.le

  calc
    v - u =
        (k : ℝ) * ((v - u) / (k : ℝ)) := by
          field_simp [ne_of_gt hkR]
    _ ≤ (k : ℝ) * (2 * root) := hmul
    _ = 2 * (k : ℝ) *
        (eps / lam) ^ ((k : ℝ)⁻¹) := by
          dsimp [root]
          ring


/-- Any finite collection of points in one level set has cardinality at
most `k`, provided the kth derivative is bounded away from zero. -/
theorem level_hit_finset_card_le
    {g : ℝ → ℝ} {k : ℕ} {a b t lam : ℝ}
    (hk : 0 < k)
    (hcont :
      ∀ r : ℕ,
        ContinuousOn (iteratedDeriv r g) (Set.Icc a b))
    (hlam : 0 < lam)
    (hlow :
      ∀ x ∈ Set.Icc a b,
        lam ≤ |iteratedDeriv k g x|)
    (s : Finset ℝ)
    (hs :
      ∀ x ∈ s,
        x ∈ Set.Icc a b ∧ g x = t) :
    s.card ≤ k := by
  by_contra hcard

  have hk1 :
      k + 1 ≤ s.card := by
    omega

  obtain ⟨r, hrs, hrcard⟩ :=
    Finset.exists_subset_card_eq (s := s) hk1

  let x : Fin (k + 1) → ℝ :=
    fun i => r.orderEmbOfFin hrcard i

  have hxmono :
      StrictMono x := by
    exact (r.orderEmbOfFin hrcard).strictMono

  have hxmem :
      ∀ i, x i ∈ Set.Icc a b := by
    intro i
    have hri : x i ∈ r := by
      simp [x]
    exact (hs (x i) (hrs hri)).1

  have hxlevel :
      ∀ i, g (x i) = t := by
    intro i
    have hri : x i ∈ r := by
      simp [x]
    exact (hs (x i) (hrs hri)).2

  apply
    (not_exists_many_level_hits_of_iteratedDeriv_abs_lower_bound
      (g := g) (k := k) (a := a) (b := b)
      (t := t) (lam := lam)
      hk hcont hlam hlow)

  exact ⟨x, hxmono, hxmem, hxlevel⟩


/-- A level set inside the interval is finite when the kth derivative
is bounded away from zero. -/
theorem level_hit_set_finite
    {g : ℝ → ℝ} {k : ℕ} {a b t lam : ℝ}
    (hk : 0 < k)
    (hcont :
      ∀ r : ℕ,
        ContinuousOn (iteratedDeriv r g) (Set.Icc a b))
    (hlam : 0 < lam)
    (hlow :
      ∀ x ∈ Set.Icc a b,
        lam ≤ |iteratedDeriv k g x|) :
    Set.Finite
      {x : ℝ | x ∈ Set.Icc a b ∧ g x = t} := by

  by_contra hfinite

  have hinfinite :
      Set.Infinite
        {x : ℝ | x ∈ Set.Icc a b ∧ g x = t} :=
    hfinite

  obtain ⟨s, hs, hcard⟩ :=
    hinfinite.exists_subset_card_eq (k + 1)

  have hle :
      s.card ≤ k := by
    apply
      level_hit_finset_card_le
        (g := g) (k := k)
        (a := a) (b := b)
        (t := t) (lam := lam)
        hk hcont hlam hlow s
    intro x hx
    have hxs : x ∈ (s : Set ℝ) := hx
    exact hs hxs

  have hbad : k + 1 ≤ k := by
    calc
      k + 1 = s.card := hcard.symm
      _ ≤ k := hle

  omega


/-- The two boundary levels `g = eps` and `g = -eps` together contain
at most `2k` points inside the interval. -/
theorem two_level_set_finite_and_ncard_le
    {g : ℝ → ℝ} {k : ℕ} {a b eps lam : ℝ}
    (hk : 0 < k)
    (hcont :
      ∀ r : ℕ,
        ContinuousOn (iteratedDeriv r g) (Set.Icc a b))
    (hlam : 0 < lam)
    (hlow :
      ∀ x ∈ Set.Icc a b,
        lam ≤ |iteratedDeriv k g x|) :
    let P : Set ℝ :=
      {x | x ∈ Set.Icc a b ∧ g x = eps}
    let M : Set ℝ :=
      {x | x ∈ Set.Icc a b ∧ g x = -eps}
    (P ∪ M).Finite ∧ (P ∪ M).ncard ≤ 2 * k := by

  let P : Set ℝ :=
    {x | x ∈ Set.Icc a b ∧ g x = eps}

  let M : Set ℝ :=
    {x | x ∈ Set.Icc a b ∧ g x = -eps}

  have hPfin : P.Finite := by
    dsimp [P]
    exact
      level_hit_set_finite
        (g := g) (k := k)
        (a := a) (b := b)
        (t := eps) (lam := lam)
        hk hcont hlam hlow

  have hMfin : M.Finite := by
    dsimp [M]
    exact
      level_hit_set_finite
        (g := g) (k := k)
        (a := a) (b := b)
        (t := -eps) (lam := lam)
        hk hcont hlam hlow

  have hPcard : P.ncard ≤ k := by
    rw [Set.ncard_eq_toFinset_card P hPfin]
    apply
      level_hit_finset_card_le
        (g := g) (k := k)
        (a := a) (b := b)
        (t := eps) (lam := lam)
        hk hcont hlam hlow hPfin.toFinset
    intro x hx
    exact hPfin.mem_toFinset.mp hx

  have hMcard : M.ncard ≤ k := by
    rw [Set.ncard_eq_toFinset_card M hMfin]
    apply
      level_hit_finset_card_le
        (g := g) (k := k)
        (a := a) (b := b)
        (t := -eps) (lam := lam)
        hk hcont hlam hlow hMfin.toFinset
    intro x hx
    exact hMfin.mem_toFinset.mp hx

  refine ⟨hPfin.union hMfin, ?_⟩

  calc
    (P ∪ M).ncard
        ≤ P.ncard + M.ncard :=
      Set.ncard_union_le P M
    _ ≤ k + k :=
      Nat.add_le_add hPcard hMcard
    _ = 2 * k := by
      omega



open Set
open MeasureTheory
open scoped Interval

/-- The absolute-value boundary of a sublevel set contains at most `2k`
points when the kth derivative is bounded away from zero. -/
theorem abs_boundary_set_finite_and_ncard_le
    {g : ℝ → ℝ} {k : ℕ} {a b eps lam : ℝ}
    (hk : 0 < k)
    (hcont :
      ∀ r : ℕ,
        ContinuousOn (iteratedDeriv r g) (Icc a b))
    (hlam : 0 < lam)
    (hlow :
      ∀ x ∈ Icc a b,
        lam ≤ |iteratedDeriv k g x|) :
    let B : Set ℝ :=
      {x | x ∈ Icc a b ∧ |g x| = eps}
    B.Finite ∧ B.ncard ≤ 2 * k := by

  let B : Set ℝ :=
    {x | x ∈ Icc a b ∧ |g x| = eps}

  let P : Set ℝ :=
    {x | x ∈ Icc a b ∧ g x = eps}

  let M : Set ℝ :=
    {x | x ∈ Icc a b ∧ g x = -eps}

  have hPM :
      (P ∪ M).Finite ∧ (P ∪ M).ncard ≤ 2 * k := by
    simpa [P, M] using
      two_level_set_finite_and_ncard_le
        (g := g) (k := k)
        (a := a) (b := b)
        (eps := eps) (lam := lam)
        hk hcont hlam hlow

  have hBsub :
      B ⊆ P ∪ M := by
    intro x hx
    rcases hx with ⟨hxab, habs⟩
    by_cases hx0 : 0 ≤ g x
    · left
      exact ⟨hxab, by
        simpa [abs_of_nonneg hx0] using habs⟩
    · right
      have hxnonpos : g x ≤ 0 :=
        le_of_not_ge hx0
      refine ⟨hxab, ?_⟩
      rw [abs_of_nonpos hxnonpos] at habs
      linarith

  have hBfin : B.Finite :=
    hPM.1.subset hBsub

  refine ⟨hBfin, ?_⟩
  exact
    (Set.ncard_le_ncard hBsub hPM.1).trans hPM.2

/-- A boundary-free gap contributes at most one sublevel interval, hence
has sublevel measure bounded by the one-dimensional interval estimate. -/
theorem sublevel_gap_measure_bound
    {g : ℝ → ℝ} {k : ℕ}
    {a b u v eps lam : ℝ}
    (hk : 0 < k)
    (huv : u ≤ v)
    (hcont :
      ∀ r : ℕ,
        ContinuousOn (iteratedDeriv r g) (Icc a b))
    (hdiff :
      ∀ r : ℕ, ∀ z ∈ Icc a b,
        DifferentiableAt ℝ (iteratedDeriv r g) z)
    (hseg : Icc u v ⊆ Icc a b)
    (heps : 0 ≤ eps)
    (hlam : 0 < lam)
    (hlow :
      ∀ x ∈ Icc a b,
        lam ≤ |iteratedDeriv k g x|)
    (hno :
      ∀ x ∈ Ioo u v,
        |g x| ≠ eps) :
    volume.real
        {x : ℝ | x ∈ Icc u v ∧ ‖g x‖ ≤ eps}
      ≤
        2 * (k : ℝ) *
          (eps / lam) ^ ((k : ℝ)⁻¹) := by

  let L : ℝ :=
    2 * (k : ℝ) *
      (eps / lam) ^ ((k : ℝ)⁻¹)

  have hL : 0 ≤ L := by
    dsimp [L]
    have hq : 0 ≤ eps / lam :=
      div_nonneg heps hlam.le
    exact mul_nonneg
      (mul_nonneg (by norm_num) (Nat.cast_nonneg k))
      (Real.rpow_nonneg hq _)

  have hgcont :
      ContinuousOn g (Icc a b) := by
    simpa using hcont 0

  have hgnorm :
      ContinuousOn (fun x => ‖g x‖) (Icc a b) :=
    hgcont.norm

  by_cases huvEq : u = v
  · subst v
    have hsub :
        {x : ℝ | x ∈ Icc u u ∧ ‖g x‖ ≤ eps}
          ⊆ ({u} : Set ℝ) := by
      intro x hx
      simpa using hx.1
    have hvol0 :
        volume ({u} : Set ℝ) = 0 :=
      Real.volume_singleton

    have hz :
        volume.real ({u} : Set ℝ) = 0 := by
      rw [measureReal_def, hvol0]
      simp

    have htop :
        volume ({u} : Set ℝ) ≠ ⊤ := by
      rw [hvol0]
      simp

    calc
      volume.real
          {x : ℝ | x ∈ Icc u u ∧ ‖g x‖ ≤ eps}
          ≤ volume.real ({u} : Set ℝ) :=
        measureReal_mono hsub htop
      _ = 0 := hz
      _ ≤ L := hL

  have huvlt : u < v :=
    lt_of_le_of_ne huv huvEq

  by_cases hex :
      ∃ x ∈ Ioo u v, ‖g x‖ ≤ eps

  · obtain ⟨x, hxuv, hxE⟩ := hex

    have hxlt : ‖g x‖ < eps := by
      have hxne : ‖g x‖ ≠ eps := by
        intro h
        apply hno x hxuv
        simpa [Real.norm_eq_abs] using h
      exact lt_of_le_of_ne hxE hxne

    have hinterior :
        ∀ y ∈ Ioo u v, ‖g y‖ ≤ eps := by
      intro y hyuv
      by_contra hy
      have hygt : eps < ‖g y‖ :=
        lt_of_not_ge hy

      have hxy :
          [[x, y]] ⊆ Icc a b := by
        apply uIcc_subset_Icc
        · apply hseg
          exact ⟨hxuv.1.le, hxuv.2.le⟩
        · apply hseg
          exact ⟨hyuv.1.le, hyuv.2.le⟩

      have hcontxy :
          ContinuousOn (fun z => ‖g z‖) [[x, y]] :=
        hgnorm.mono hxy

      have htarget :
          eps ∈ [[‖g x‖, ‖g y‖]] := by
        rw [uIcc_of_le (hxE.trans hygt.le)]
        exact ⟨hxlt.le, hygt.le⟩

      obtain ⟨z, hzxy, hzeq⟩ :=
        intermediate_value_uIcc hcontxy htarget

      have hzuv : z ∈ Ioo u v :=
        ordConnected_Ioo.uIcc_subset hxuv hyuv hzxy

      apply hno z hzuv
      simpa [Real.norm_eq_abs] using hzeq

    have hlength : v - u ≤ L := by
      by_contra hlen
      have hlong : L < v - u :=
        lt_of_not_ge hlen

      let d : ℝ := (v - u - L) / 4
      let p : ℝ := u + d
      let q : ℝ := v - d

      have hd : 0 < d := by
        dsimp [d]
        linarith

      have h2d : 2 * d < v - u := by
        dsimp [d]
        linarith

      have hpq : p < q := by
        dsimp [p, q]
        linarith

      have hpIoo : p ∈ Ioo u v := by
        constructor
        · dsimp [p]
          linarith
        · dsimp [p]
          linarith

      have hqIoo : q ∈ Ioo u v := by
        constructor
        · dsimp [q]
          linarith
        · dsimp [q]
          linarith

      have hpqseg :
          Icc p q ⊆ Icc a b := by
        intro z hz
        apply hseg
        constructor
        · linarith [hpIoo.1, hz.1]
        · linarith [hqIoo.2, hz.2]

      have hpqbound :
          ∀ z ∈ Icc p q, ‖g z‖ ≤ eps := by
        intro z hz
        apply hinterior z
        constructor
        · linarith [hpIoo.1, hz.1]
        · linarith [hqIoo.2, hz.2]

      have hpqlow :
          ∀ z ∈ Icc p q,
            lam ≤ |iteratedDeriv k g z| := by
        intro z hz
        exact hlow z (hpqseg hz)

      have hpqLen :=
        sublevel_interval_length_bound
          (g := g) (k := k)
          (a := a) (b := b)
          (u := p) (v := q)
          (eps := eps) (lam := lam)
          hk hpq hdiff hpqseg heps hlam
          hpqbound hpqlow

      have hpqLong : L < q - p := by
        dsimp [p, q, d]
        linarith

      have hpqLen' : q - p ≤ L := by
        simpa [L] using hpqLen
      exact (not_lt_of_ge hpqLen') hpqLong

    calc
      volume.real
          {x : ℝ | x ∈ Icc u v ∧ ‖g x‖ ≤ eps}
          ≤ volume.real (Icc u v) := by
            apply measureReal_mono
            · intro z hz
              exact hz.1
            · simp [Real.volume_Icc]
      _ = v - u :=
        Real.volume_real_Icc_of_le huv
      _ ≤ L := hlength

  · have hsub :
        {x : ℝ | x ∈ Icc u v ∧ ‖g x‖ ≤ eps}
          ⊆ ({u, v} : Set ℝ) := by
      intro x hx
      have hxuv := hx.1

      by_cases hxu : x = u
      · simp [hxu]

      by_cases hxv : x = v
      · simp [hxv]

      have hux : u < x :=
        lt_of_le_of_ne hxuv.1 (Ne.symm hxu)

      have hxv' : x < v :=
        lt_of_le_of_ne hxuv.2 hxv

      exfalso
      apply hex
      exact ⟨x, ⟨hux, hxv'⟩, hx.2⟩

    have hpairEq :
        ({u, v} : Set ℝ) =
          ({u} : Set ℝ) ∪ ({v} : Set ℝ) := by
      ext z
      simp [or_comm]

    have hvolPair :
        volume ({u, v} : Set ℝ) = 0 := by
      apply le_antisymm
      · rw [hpairEq]
        calc
          volume (({u} : Set ℝ) ∪ ({v} : Set ℝ))
              ≤ volume ({u} : Set ℝ) +
                  volume ({v} : Set ℝ) :=
            measure_union_le _ _
          _ = 0 := by
            rw [Real.volume_singleton, Real.volume_singleton]
            simp
      · exact bot_le

    have hz :
        volume.real ({u, v} : Set ℝ) = 0 := by
      rw [measureReal_def, hvolPair]
      simp

    have htop :
        volume ({u, v} : Set ℝ) ≠ ⊤ := by
      rw [hvolPair]
      simp

    calc
      volume.real
          {x : ℝ | x ∈ Icc u v ∧ ‖g x‖ ≤ eps}
          ≤ volume.real ({u, v} : Set ℝ) :=
        measureReal_mono hsub htop
      _ = 0 := hz
      _ ≤ L := hL


/-- Inductive measure estimate in terms of a finite set containing
all interior boundary points `|g| = eps`. -/
theorem sublevel_measure_le_of_boundary_finset_aux
    (n : ℕ)
    {g : ℝ → ℝ} {k : ℕ}
    {a b eps lam : ℝ}
    (hk : 0 < k)
    (hab : a ≤ b)
    (hcont :
      ∀ r : ℕ,
        ContinuousOn (iteratedDeriv r g) (Icc a b))
    (hdiff :
      ∀ r : ℕ, ∀ z ∈ Icc a b,
        DifferentiableAt ℝ (iteratedDeriv r g) z)
    (heps : 0 ≤ eps)
    (hlam : 0 < lam)
    (hlow :
      ∀ x ∈ Icc a b,
        lam ≤ |iteratedDeriv k g x|)
    (B : Finset ℝ)
    (hcard : B.card ≤ n)
    (hBmem :
      ∀ x ∈ B,
        x ∈ Ioo a b ∧ |g x| = eps)
    (hBcover :
      ∀ x ∈ Ioo a b,
        |g x| = eps → x ∈ B) :
    volume.real
        {x : ℝ | x ∈ Icc a b ∧ ‖g x‖ ≤ eps}
      ≤
        ((B.card + 1 : ℕ) : ℝ) *
          (2 * (k : ℝ) *
            (eps / lam) ^ ((k : ℝ)⁻¹)) := by

  classical

  induction n generalizing a b B with

  | zero =>
      have hBzero : B.card = 0 :=
        Nat.eq_zero_of_le_zero hcard

      have hBempty : B = ∅ :=
        Finset.card_eq_zero.mp hBzero

      have hno :
          ∀ x ∈ Ioo a b, |g x| ≠ eps := by
        intro x hx heq
        have hxB := hBcover x hx heq
        rw [hBempty] at hxB
        simp at hxB

      have hgap :=
        sublevel_gap_measure_bound
          (g := g) (k := k)
          (a := a) (b := b)
          (u := a) (v := b)
          (eps := eps) (lam := lam)
          hk hab hcont hdiff
          (by intro x hx; exact hx)
          heps hlam hlow hno

      rw [hBempty]
      simpa using hgap

  | succ n ih =>
      by_cases hBempty : B = ∅

      · have hno :
            ∀ x ∈ Ioo a b, |g x| ≠ eps := by
          intro x hx heq
          have hxB := hBcover x hx heq
          rw [hBempty] at hxB
          simp at hxB

        have hgap :=
          sublevel_gap_measure_bound
            (g := g) (k := k)
            (a := a) (b := b)
            (u := a) (v := b)
            (eps := eps) (lam := lam)
            hk hab hcont hdiff
            (by intro x hx; exact hx)
            heps hlam hlow hno

        rw [hBempty]
        simpa using hgap

      · have hBne : B.Nonempty :=
          Finset.nonempty_iff_ne_empty.mpr hBempty

        let c : ℝ := B.min' hBne

        have hcB : c ∈ B := by
          dsimp [c]
          exact B.min'_mem hBne

        have hcdata :=
          hBmem c hcB

        have hac : a < c :=
          hcdata.1.1

        have hcb : c < b :=
          hcdata.1.2

        let R : Finset ℝ := B.erase c
        let BL : Finset ℝ :=
          R.filter (fun x => x < c)
        let BR : Finset ℝ :=
          R.filter (fun x => ¬ x < c)

        have hRlt : R.card < B.card := by
          dsimp [R]
          exact Finset.card_erase_lt_of_mem hcB

        have hRle : R.card ≤ n := by
          omega

        have hBLcard : BL.card ≤ n := by
          exact (Finset.card_filter_le R _).trans hRle

        have hBRcard : BR.card ≤ n := by
          exact (Finset.card_filter_le R _).trans hRle

        have hleftSub :
            Icc a c ⊆ Icc a b :=
          Icc_subset_Icc le_rfl hcb.le

        have hrightSub :
            Icc c b ⊆ Icc a b :=
          Icc_subset_Icc hac.le le_rfl

        have hcontL :
            ∀ r : ℕ,
              ContinuousOn
                (iteratedDeriv r g) (Icc a c) :=
          fun r => (hcont r).mono hleftSub

        have hcontR :
            ∀ r : ℕ,
              ContinuousOn
                (iteratedDeriv r g) (Icc c b) :=
          fun r => (hcont r).mono hrightSub

        have hdiffL :
            ∀ r : ℕ, ∀ z ∈ Icc a c,
              DifferentiableAt ℝ
                (iteratedDeriv r g) z := by
          intro r z hz
          exact hdiff r z (hleftSub hz)

        have hdiffR :
            ∀ r : ℕ, ∀ z ∈ Icc c b,
              DifferentiableAt ℝ
                (iteratedDeriv r g) z := by
          intro r z hz
          exact hdiff r z (hrightSub hz)

        have hlowL :
            ∀ z ∈ Icc a c,
              lam ≤ |iteratedDeriv k g z| := by
          intro z hz
          exact hlow z (hleftSub hz)

        have hlowR :
            ∀ z ∈ Icc c b,
              lam ≤ |iteratedDeriv k g z| := by
          intro z hz
          exact hlow z (hrightSub hz)

        have hBmemL :
            ∀ x ∈ BL,
              x ∈ Ioo a c ∧ |g x| = eps := by
          intro x hx
          have hxF := Finset.mem_filter.mp hx
          have hxR : x ∈ R := hxF.1
          have hxc : x < c := hxF.2

          have hxErase : x ∈ B.erase c := by
            simpa [R] using hxR

          have hxB : x ∈ B :=
            Finset.mem_of_mem_erase hxErase

          have hxData := hBmem x hxB

          exact
            ⟨⟨hxData.1.1, hxc⟩, hxData.2⟩

        have hBmemR :
            ∀ x ∈ BR,
              x ∈ Ioo c b ∧ |g x| = eps := by
          intro x hx
          have hxF := Finset.mem_filter.mp hx
          have hxR : x ∈ R := hxF.1
          have hxNot : ¬ x < c := hxF.2

          have hxErase : x ∈ B.erase c := by
            simpa [R] using hxR

          have hxNe : x ≠ c :=
            Finset.ne_of_mem_erase hxErase

          have hxB : x ∈ B :=
            Finset.mem_of_mem_erase hxErase

          have hxData := hBmem x hxB

          have hcx : c < x := by
            have hcxle : c ≤ x :=
              le_of_not_gt hxNot
            exact lt_of_le_of_ne
              hcxle (Ne.symm hxNe)

          exact
            ⟨⟨hcx, hxData.1.2⟩, hxData.2⟩

        have hBcoverL :
            ∀ x ∈ Ioo a c,
              |g x| = eps → x ∈ BL := by
          intro x hx heq

          have hxB :
              x ∈ B :=
            hBcover x
              ⟨hx.1, hx.2.trans hcb⟩ heq

          have hxErase :
              x ∈ B.erase c :=
            Finset.mem_erase_of_ne_of_mem
              (ne_of_lt hx.2) hxB

          apply Finset.mem_filter.mpr
          constructor
          · simpa [R] using hxErase
          · exact hx.2

        have hBcoverR :
            ∀ x ∈ Ioo c b,
              |g x| = eps → x ∈ BR := by
          intro x hx heq

          have hxB :
              x ∈ B :=
            hBcover x
              ⟨hac.trans hx.1, hx.2⟩ heq

          have hxErase :
              x ∈ B.erase c :=
            Finset.mem_erase_of_ne_of_mem
              (ne_of_gt hx.1) hxB

          apply Finset.mem_filter.mpr
          constructor
          · simpa [R] using hxErase
          · exact not_lt.mpr hx.1.le

        have hleft :=
          ih hac.le hcontL hdiffL hlowL
            BL hBLcard hBmemL hBcoverL

        have hright :=
          ih hcb.le hcontR hdiffR hlowR
            BR hBRcard hBmemR hBcoverR

        have hsplit :
            BL.card + BR.card = R.card := by
          dsimp [BL, BR]
          exact
            R.filter_card_add_filter_neg_card_eq_card
              (fun x : ℝ => x < c)

        have hRadd :
            R.card + 1 = B.card := by
          dsimp [R]
          exact B.card_erase_add_one hcB

        have hcount :
            BL.card + BR.card + 2 =
              B.card + 1 := by
          omega

        let EL : Set ℝ :=
          {x | x ∈ Icc a c ∧ ‖g x‖ ≤ eps}

        let ER : Set ℝ :=
          {x | x ∈ Icc c b ∧ ‖g x‖ ≤ eps}

        let E : Set ℝ :=
          {x | x ∈ Icc a b ∧ ‖g x‖ ≤ eps}

        have hEcover :
            E ⊆ EL ∪ ER := by
          intro x hx
          rcases hx with ⟨hxI, hxg⟩
          rcases le_total x c with hxc | hcx
          · left
            exact ⟨⟨hxI.1, hxc⟩, hxg⟩
          · right
            exact ⟨⟨hcx, hxI.2⟩, hxg⟩

        have hUnionSub :
            EL ∪ ER ⊆ Icc a b := by
          intro x hx
          rcases hx with hx | hx
          · exact hleftSub hx.1
          · exact hrightSub hx.1

        have hmono :
            volume.real E
              ≤ volume.real (EL ∪ ER) := by
          exact
            measureReal_mono hEcover
              (measure_ne_top_of_subset
                hUnionSub (by simp [Real.volume_Icc]))

        have hunion :
            volume.real (EL ∪ ER)
              ≤ volume.real EL + volume.real ER :=
          measureReal_union_le EL ER

        have hcount' :
            (BL.card + 1) + (BR.card + 1)
              = B.card + 1 := by
          omega

        have hcast :
            (((BL.card + 1 : ℕ) : ℝ) +
                ((BR.card + 1 : ℕ) : ℝ))
              =
            ((B.card + 1 : ℕ) : ℝ) := by
          exact_mod_cast hcount' 

        change volume.real E ≤
          ((B.card + 1 : ℕ) : ℝ) *
            (2 * (k : ℝ) *
              (eps / lam) ^ ((k : ℝ)⁻¹))

        calc
          volume.real E
              ≤ volume.real (EL ∪ ER) := hmono
          _ ≤ volume.real EL + volume.real ER :=
              hunion
          _ ≤
              ((BL.card + 1 : ℕ) : ℝ) *
                  (2 * (k : ℝ) *
                    (eps / lam) ^ ((k : ℝ)⁻¹))
              +
              ((BR.card + 1 : ℕ) : ℝ) *
                  (2 * (k : ℝ) *
                    (eps / lam) ^ ((k : ℝ)⁻¹)) :=
            add_le_add hleft hright
          _ =
              ((((BL.card + 1 : ℕ) : ℝ) +
                ((BR.card + 1 : ℕ) : ℝ)) *
                  (2 * (k : ℝ) *
                    (eps / lam) ^ ((k : ℝ)⁻¹))) := by
            ring
          _ =
              ((B.card + 1 : ℕ) : ℝ) *
                (2 * (k : ℝ) *
                  (eps / lam) ^ ((k : ℝ)⁻¹)) := by
            rw [hcast]


/-- One-dimensional sublevel estimate with the explicit constant used in
Lemma 3.4. The bound `# {|g| = eps} ≤ 2k` supplies the `2k+1`
interval factor. -/
theorem sublevel_measure_bound
    {g : ℝ → ℝ} {k : ℕ}
    {a b eps lam : ℝ}
    (hk : 0 < k)
    (hab : a ≤ b)
    (hcont :
      ∀ r : ℕ,
        ContinuousOn (iteratedDeriv r g) (Icc a b))
    (hdiff :
      ∀ r : ℕ, ∀ z ∈ Icc a b,
        DifferentiableAt ℝ (iteratedDeriv r g) z)
    (heps : 0 ≤ eps)
    (hlam : 0 < lam)
    (hlow :
      ∀ x ∈ Icc a b,
        lam ≤ |iteratedDeriv k g x|) :
    volume.real
        {x : ℝ | x ∈ Icc a b ∧ ‖g x‖ ≤ eps}
      ≤
        2 * (k : ℝ) *
          (2 * (k : ℝ) + 1) *
          (eps / lam) ^ ((k : ℝ)⁻¹) := by

  let BC : Set ℝ :=
    {x | x ∈ Icc a b ∧ |g x| = eps}

  let BI : Set ℝ :=
    {x | x ∈ Ioo a b ∧ |g x| = eps}

  have hBC :
      BC.Finite ∧ BC.ncard ≤ 2 * k := by
    simpa [BC] using
      abs_boundary_set_finite_and_ncard_le
        (g := g) (k := k)
        (a := a) (b := b)
        (eps := eps) (lam := lam)
        hk hcont hlam hlow

  have hBI_sub :
      BI ⊆ BC := by
    intro x hx
    exact
      ⟨⟨hx.1.1.le, hx.1.2.le⟩, hx.2⟩

  have hBIfin : BI.Finite :=
    hBC.1.subset hBI_sub

  have hBIcard :
      BI.ncard ≤ 2 * k :=
    (Set.ncard_le_ncard hBI_sub hBC.1).trans hBC.2

  let B : Finset ℝ :=
    hBIfin.toFinset

  have hBcard :
      B.card ≤ 2 * k := by
    dsimp [B]
    rw [← Set.ncard_eq_toFinset_card BI hBIfin]
    exact hBIcard

  have hBmem :
      ∀ x ∈ B,
        x ∈ Ioo a b ∧ |g x| = eps := by
    intro x hx
    exact hBIfin.mem_toFinset.mp hx

  have hBcover :
      ∀ x ∈ Ioo a b,
        |g x| = eps → x ∈ B := by
    intro x hx heq
    apply hBIfin.mem_toFinset.mpr
    exact ⟨hx, heq⟩

  have haux :=
    sublevel_measure_le_of_boundary_finset_aux
      B.card
      (g := g) (k := k)
      (a := a) (b := b)
      (eps := eps) (lam := lam)
      hk hab hcont hdiff heps hlam hlow
      B le_rfl hBmem hBcover

  have hq : 0 ≤ eps / lam :=
    div_nonneg heps hlam.le

  have hroot :
      0 ≤
        (eps / lam) ^ ((k : ℝ)⁻¹) :=
    Real.rpow_nonneg hq _

  have hL :
      0 ≤
        2 * (k : ℝ) *
          (eps / lam) ^ ((k : ℝ)⁻¹) := by
    exact mul_nonneg
      (mul_nonneg (by norm_num) (Nat.cast_nonneg k))
      hroot

  have hcoef :
      ((B.card + 1 : ℕ) : ℝ)
        ≤ 2 * (k : ℝ) + 1 := by
    exact_mod_cast
      Nat.add_le_add_right hBcard 1

  calc
    volume.real
        {x : ℝ | x ∈ Icc a b ∧ ‖g x‖ ≤ eps}
        ≤
      ((B.card + 1 : ℕ) : ℝ) *
        (2 * (k : ℝ) *
          (eps / lam) ^ ((k : ℝ)⁻¹)) :=
      haux
    _ ≤
      (2 * (k : ℝ) + 1) *
        (2 * (k : ℝ) *
          (eps / lam) ^ ((k : ℝ)⁻¹)) :=
      mul_le_mul_of_nonneg_right hcoef hL
    _ =
      2 * (k : ℝ) *
        (2 * (k : ℝ) + 1) *
        (eps / lam) ^ ((k : ℝ)⁻¹) := by
      ring


end MahlerLean
