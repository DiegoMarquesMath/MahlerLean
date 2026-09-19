import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Order.Fin.Basic
import MahlerLean.UniformJet

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

end MahlerLean
