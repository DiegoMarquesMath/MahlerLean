import MahlerLean.RationalTaylorBasis
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Topology.Instances.Matrix

noncomputable section
open Filter Set
open scoped Topology
namespace MahlerLean

/-- Taylor's leading coefficient, stated on the punctured neighborhood. -/
theorem tendsto_div_pow_of_analytic_vanishing {g : ℝ → ℝ} {z : ℝ} {n : ℕ}
    (hg : AnalyticAt ℝ g z) (hz : ∀ k < n, iteratedDeriv k g z = 0) :
    Tendsto (fun x ↦ g x / (x-z)^n) (𝓝[≠] z)
      (𝓝 (iteratedDeriv n g z / (n.factorial : ℝ))) := by
  obtain ⟨ε, hε, ha⟩ := hg.exists_ball_analyticOnNhd
  have hb : Metric.ball z ε ∈ 𝓝 z := Metric.ball_mem_nhds z hε
  have hc : ContDiffOn ℝ n g (Metric.ball z ε) := ha.contDiffOn Metric.isOpen_ball.uniqueDiffOn
  have ht := Real.taylor_tendsto (convex_ball z ε) (Metric.mem_ball_self hε) hc
  rw [nhdsWithin_eq_nhds.mpr hb] at ht
  have hp : ∀ x, taylorWithinEval g n (Metric.ball z ε) z x =
      (iteratedDeriv n g z / (n.factorial : ℝ)) * (x-z)^n := by
    intro x
    rw [taylor_within_apply, Finset.sum_range_succ]
    have hzero : ∑ k ∈ Finset.range n,
        ((k.factorial : ℝ)⁻¹ * (x-z)^k) • iteratedDerivWithin k g (Metric.ball z ε) z = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [iteratedDerivWithin_of_isOpen Metric.isOpen_ball (Metric.mem_ball_self hε),
        hz k (Finset.mem_range.mp hk)]
      simp
    rw [hzero, zero_add, iteratedDerivWithin_of_isOpen Metric.isOpen_ball (Metric.mem_ball_self hε)]
    simp only [smul_eq_mul, div_eq_mul_inv]
    ring
  have ht' := (ht.mono_left (nhdsWithin_le_nhds (s := {z}ᶜ))).add_const
    (iteratedDeriv n g z / (n.factorial : ℝ))
  simp only [zero_add] at ht'
  apply ht'.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hxz : x-z ≠ 0 := sub_ne_zero.mpr hx
  rw [hp]
  field_simp
  ring

/-- A scaled derivative retains the falling-factorial leading coefficient,
including derivative orders larger than the order of vanishing. -/
theorem tendsto_scaled_iteratedDeriv {g : ℝ → ℝ} {z : ℝ} {r : ℕ}
    (hg : AnalyticAt ℝ g z) (hz : ∀ k < r, iteratedDeriv k g z = 0) (i : ℕ) :
    Tendsto (fun x ↦ (x-z)^i * iteratedDeriv i g x / (x-z)^r) (𝓝[≠] z)
      (𝓝 ((iteratedDeriv r g z / (r.factorial : ℝ)) * (r.descFactorial i : ℝ))) := by
  have hgi : AnalyticAt ℝ (iteratedDeriv i g) z := by
    simpa only [iteratedDeriv_eq_iterate] using hg.iterated_deriv i
  by_cases hir : i ≤ r
  · have hcomp (k : ℕ) : iteratedDeriv k (iteratedDeriv i g) = iteratedDeriv (k+i) g := by
      simp only [iteratedDeriv_eq_iterate, Function.iterate_add_apply]
    have hlim := tendsto_div_pow_of_analytic_vanishing (n := r-i) hgi (by
      intro k hk
      rw [hcomp]
      exact hz (k+i) (by omega))
    rw [hcomp, Nat.sub_add_cancel hir] at hlim
    have hfac : ((r-i).factorial : ℝ) * (r.descFactorial i : ℝ) = (r.factorial : ℝ) := by
      exact_mod_cast Nat.factorial_mul_descFactorial hir
    have hcoeff : iteratedDeriv r g z / ((r-i).factorial : ℝ) =
        iteratedDeriv r g z / (r.factorial : ℝ) * (r.descFactorial i : ℝ) := by
      have h1 : ((r-i).factorial : ℝ) ≠ 0 := by positivity
      have h2 : (r.factorial : ℝ) ≠ 0 := by positivity
      field_simp
      rw [mul_assoc, hfac]
    rw [hcoeff] at hlim
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hne : x-z ≠ 0 := sub_ne_zero.mpr hx
    have hp : (x-z)^r = (x-z)^(r-i) * (x-z)^i := by
      rw [← pow_add, Nat.sub_add_cancel hir]
    rw [hp]
    field_simp
  · have hri : r < i := by omega
    rw [Nat.descFactorial_of_lt hri, Nat.cast_zero, mul_zero]
    have hpow : Tendsto (fun x : ℝ ↦ (x-z)^(i-r)) (𝓝[≠] z) (𝓝 0) := by
      have h := ((tendsto_id.sub_const z).pow (i-r)).mono_left
        (nhdsWithin_le_nhds (a := z) (s := {z}ᶜ))
      simpa [Nat.sub_ne_zero_of_lt hri] using h
    have hlim := hpow.mul (hgi.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds (s := {z}ᶜ)))
    simp only [zero_mul] at hlim
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hne : x-z ≠ 0 := sub_ne_zero.mpr hx
    have hp : (x-z)^i = (x-z)^(i-r) * (x-z)^r := by
      rw [← pow_add, Nat.sub_add_cancel hri.le]
    rw [hp]
    field_simp

/-- The exact normalization of the derivative determinant. -/
theorem det_scaled_derivatives {N : ℕ} (φ : Fin N → ℝ → ℝ)
    (r : Fin N → ℕ) (z x : ℝ) :
    Matrix.det (fun i j : Fin N ↦ (x-z)^i.val * iteratedDeriv i.val (φ j) x / (x-z)^(r j)) =
      (x-z)^(∑ i : Fin N, i.val) * wronskian φ x / (x-z)^(∑ j, r j) := by
  classical
  have hm : (fun i j : Fin N ↦ (x-z)^i.val * iteratedDeriv i.val (φ j) x / (x-z)^(r j)) =
      Matrix.of (fun i j : Fin N ↦ (x-z)^i.val *
        (Matrix.of (fun i j : Fin N ↦ ((x-z)^(r j))⁻¹ * iteratedDeriv i.val (φ j) x)) i j) := by
    funext i j
    simp only [Matrix.of_apply, div_eq_mul_inv]
    ring
  rw [hm, Matrix.det_mul_column, Matrix.det_mul_row]
  simp only [Finset.prod_inv_distrib, Finset.prod_pow_eq_pow_sum, wronskian, div_eq_mul_inv]
  ring

/-- The leading coefficient of the analytic Wronskian. The product of column
Taylor coefficients multiplies the falling-factorial (Vandermonde) determinant. -/
theorem tendsto_wronskian_leading_coefficient {N : ℕ} (φ : Fin N → ℝ → ℝ)
    (r : Fin N → ℕ) {z : ℝ} (hφ : ∀ j, AnalyticAt ℝ (φ j) z)
    (hz : ∀ j k, k < r j → iteratedDeriv k (φ j) z = 0) :
    Tendsto (fun x ↦ (x-z)^(∑ i : Fin N, i.val) * wronskian φ x / (x-z)^(∑ j, r j))
      (𝓝[≠] z) (𝓝 ((∏ j, iteratedDeriv (r j) (φ j) z / ((r j).factorial : ℝ)) *
        Matrix.det (fun i j : Fin N ↦ ((r j).descFactorial i.val : ℝ)))) := by
  classical
  have hentries := fun i j : Fin N ↦ tendsto_scaled_iteratedDeriv (hφ j) (hz j) i.val
  have hmatrix := tendsto_pi_nhds.mpr (fun i ↦ tendsto_pi_nhds.mpr (hentries i))
  have hdet := (continuous_id.matrix_det.continuousAt.tendsto).comp hmatrix
  have hcoeff : Matrix.det (fun i j : Fin N ↦
      (iteratedDeriv (r j) (φ j) z / ((r j).factorial : ℝ)) * ((r j).descFactorial i.val : ℝ)) =
      (∏ j, iteratedDeriv (r j) (φ j) z / ((r j).factorial : ℝ)) *
        Matrix.det (fun i j : Fin N ↦ ((r j).descFactorial i.val : ℝ)) :=
    Matrix.det_mul_row _ _
  simpa only [Function.comp_def, id_eq, det_scaled_derivatives, hcoeff] using hdet

/-- Distinct, finite vanishing orders force the leading coefficient to be nonzero. -/
theorem wronskian_leading_coefficient_ne_zero {N : ℕ} (φ : Fin N → ℝ → ℝ)
    (r : Fin N → ℕ) {z : ℝ} (hr : Function.Injective r)
    (hlead : ∀ j, iteratedDeriv (r j) (φ j) z ≠ 0) :
    (∏ j, iteratedDeriv (r j) (φ j) z / ((r j).factorial : ℝ)) *
      Matrix.det (fun i j : Fin N ↦ ((r j).descFactorial i.val : ℝ)) ≠ 0 := by
  apply mul_ne_zero _ (det_descFactorial_ne_zero r hr)
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  exact div_ne_zero (hlead j) (by positivity)

/-- The leading-term formula written with its single integer exponent. -/
theorem tendsto_wronskian_div_zpow {N : ℕ} (φ : Fin N → ℝ → ℝ)
    (r : Fin N → ℕ) {z : ℝ} (hφ : ∀ j, AnalyticAt ℝ (φ j) z)
    (hz : ∀ j k, k < r j → iteratedDeriv k (φ j) z = 0) :
    Tendsto (fun x ↦ wronskian φ x /
      (x-z)^((∑ j, r j : ℕ) - (∑ i : Fin N, i.val : ℕ) : ℤ))
      (𝓝[≠] z) (𝓝 ((∏ j, iteratedDeriv (r j) (φ j) z / ((r j).factorial : ℝ)) *
        Matrix.det (fun i j : Fin N ↦ ((r j).descFactorial i.val : ℝ)))) := by
  apply (tendsto_wronskian_leading_coefficient φ r hφ hz).congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hne : x-z ≠ 0 := sub_ne_zero.mpr hx
  rw [zpow_sub₀ hne, zpow_natCast, zpow_natCast]
  field_simp

/-- A Wronskian with distinct finite vanishing orders is nonzero on a
punctured neighborhood of the base point. -/
theorem eventually_wronskian_ne_zero_of_distinct_orders {N : ℕ}
    (φ : Fin N → ℝ → ℝ) (r : Fin N → ℕ) {z : ℝ}
    (hφ : ∀ j, AnalyticAt ℝ (φ j) z) (hr : Function.Injective r)
    (hlead : ∀ j, iteratedDeriv (r j) (φ j) z ≠ 0)
    (hz : ∀ j k, k < r j → iteratedDeriv k (φ j) z = 0) :
    ∀ᶠ x in 𝓝[≠] z, wronskian φ x ≠ 0 := by
  have hlim := tendsto_wronskian_leading_coefficient φ r hφ hz
  have hc := wronskian_leading_coefficient_ne_zero φ r hr hlead
  have he := hlim.eventually (isOpen_ne.mem_nhds hc)
  filter_upwards [he] with x hx
  intro hw
  apply hx
  simp [hw]

/-- Injectivity of the orders ensures that the leading exponent is a natural number. -/
theorem sum_indices_le_sum_distinct_orders {N : ℕ} (r : Fin N → ℕ)
    (hr : Function.Injective r) : (∑ i : Fin N, i.val) ≤ ∑ j, r j := by
  classical
  by_contra hn
  have hd := det_descFactorial_ne_zero r hr
  apply hd
  rw [Matrix.det_apply]
  apply Finset.sum_eq_zero
  intro σ _
  have he : ∃ j : Fin N, r j < (σ j).val := by
    by_contra h
    push_neg at h
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ h j)
    rw [Equiv.sum_comp σ (fun i : Fin N ↦ i.val)] at hs
    exact hn hs
  obtain ⟨j, hj⟩ := he
  have hp : ∏ i : Fin N, ((r i).descFactorial (σ i).val : ℝ) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [Nat.descFactorial_of_lt hj]
  rw [hp, smul_zero]

/-- Standard leading-term formula with exponent sum(r_j) - N(N-1)/2. -/
theorem tendsto_wronskian_div_pow {N : ℕ} (φ : Fin N → ℝ → ℝ)
    (r : Fin N → ℕ) {z : ℝ} (hφ : ∀ j, AnalyticAt ℝ (φ j) z)
    (hr : Function.Injective r)
    (hz : ∀ j k, k < r j → iteratedDeriv k (φ j) z = 0) :
    Tendsto (fun x ↦ wronskian φ x / (x-z)^((∑ j, r j) - N*(N-1)/2))
      (𝓝[≠] z) (𝓝 ((∏ j, iteratedDeriv (r j) (φ j) z / ((r j).factorial : ℝ)) *
        (Matrix.vandermonde (fun j ↦ (r j : ℝ))).det)) := by
  have hsum : (∑ i : Fin N, i.val) = N*(N-1)/2 := by
    exact (Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ i) N).trans (Finset.sum_range_id N)
  have hle := sum_indices_le_sum_distinct_orders r hr
  have h := tendsto_wronskian_div_zpow φ r hφ hz
  rw [← Int.natCast_sub hle] at h
  simpa only [zpow_natCast, hsum, det_descFactorial_eq_vandermonde] using h

end MahlerLean
