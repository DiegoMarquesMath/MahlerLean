import MahlerLean.IrrationalityExponent
import Mathlib.NumberTheory.Transcendental.Liouville.Residual
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.CauchyIntegral

noncomputable section
open Set Polynomial Filter
open scoped Topology
namespace MahlerLean

/-- Preservation on an open interval forces rationality. -/
theorem rationalOn_of_preserves_liouville
    {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (hconn : IsPreconnected U)
    (hne : U.Nonempty) (hf : AnalyticOnNhd ℝ f U)
    (hpres : ∀ x ∈ U, Liouville x → Liouville (f x)) : IsRationalOn f U := by
  by_contra hnr
  obtain ⟨x, hx, hL, _, B, _, havoid⟩ := theorem_1_2 hU hconn hf hnr hU hne (Subset.refl U)
  exact not_liouville_of_eventual_target_avoidance _ _ _ havoid (hpres x hx hL)

/-- Real values on the dense Liouville set imply real values everywhere on the axis. -/
theorem real_on_axis_of_preserves_liouville
    {F : ℂ → ℂ} (hF : Continuous F)
    (hpres : ∀ x : ℝ, Liouville x → ∃ y : ℝ, Liouville y ∧ F x = y) :
    ∀ x : ℝ, F x = ((F x).re : ℂ) := by
  have hc : IsClosed {x : ℝ | (F x).im = 0} :=
    isClosed_eq (Complex.continuous_im.comp (hF.comp Complex.continuous_ofReal)) continuous_const
  have hs : closure {x : ℝ | Liouville x} ⊆ {x : ℝ | (F x).im = 0} := by
    apply hc.closure_subset_iff.mpr
    intro x hx
    obtain ⟨y, _, hy⟩ := hpres x hx
    simp [hy]
  rw [dense_liouville.closure_eq] at hs
  intro x
  apply Complex.ext
  · simp
  · simpa only [Complex.ofReal_im] using hs (mem_univ x)

/-- The real part of the restriction of an entire function is real analytic. -/
theorem analytic_real_restriction {F : ℂ → ℂ} (hF : Differentiable ℂ F) :
    AnalyticOnNhd ℝ (fun x : ℝ ↦ (F x).re) univ := by
  intro x _
  exact (Complex.reCLM.analyticAt _).comp
    (((hF.analyticAt (x : ℂ)).restrictScalars (𝕜 := ℝ)).comp
      (Complex.ofRealCLM.analyticAt x))

/-- Entire functions agreeing on the real axis agree everywhere. -/
theorem entire_eq_of_eq_on_real {F G : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F univ) (hG : AnalyticOnNhd ℂ G univ)
    (hreal : ∀ x : ℝ, F x = G x) : F = G := by
  have ht : Tendsto (fun x : ℝ ↦ (x : ℂ)) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with x hx
    simpa using hx
  apply hF.eq_of_frequently_eq hG
  exact ht.frequently (Eventually.frequently (Eventually.of_forall hreal))

/-- An entire function rational on the real axis is a real polynomial. -/
theorem entire_polynomial_of_rational_real_restriction
    {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hreal : ∀ x : ℝ, F x = ((F x).re : ℂ))
    (hrat : IsRationalOn (fun x : ℝ ↦ (F x).re) univ) :
    ∃ R : Polynomial ℝ, ∀ z : ℂ, F z = R.eval₂ Complex.ofRealHom z := by
  obtain ⟨P, Q, hQ, hQx, hrel⟩ := hrat
  let ev (R : Polynomial ℝ) (z : ℂ) := (R.map Complex.ofRealHom).eval z
  have heval (R : Polynomial ℝ) (x : ℝ) : ev R x = ((Polynomial.eval x R : ℝ) : ℂ) := by
    change (R.map Complex.ofRealHom).eval (x : ℂ) = _
    rw [Polynomial.eval_map]
    exact Polynomial.eval₂_hom Complex.ofRealHom x
  have han (R : Polynomial ℝ) : AnalyticOnNhd ℂ (ev R) univ :=
    AnalyticOnNhd.eval_polynomial _
  have hFa : AnalyticOnNhd ℂ F univ := fun z _ ↦ hF.analyticAt z
  have hglobal : ∀ z : ℂ, ev Q z * F z - ev P z = 0 := by
    have he := entire_eq_of_eq_on_real (G := fun _ ↦ (0 : ℂ)) ((han Q).mul hFa |>.sub (han P))
      analyticOnNhd_const (fun x ↦ ?_)
    · intro z
      exact congrFun he z
    change ev Q x * F x - ev P x = 0
    rw [heval, heval, hreal x]
    have h := (eq_div_iff (hQx x (mem_univ x))).mp (hrel x (mem_univ x))
    exact_mod_cast (by nlinarith [h] : Q.eval x * (F x).re - P.eval x = 0)
  obtain ⟨A, B, hP, hQB, hcop⟩ := extract_gcd P Q
  have hD : gcd P Q ≠ 0 := by
    intro hz
    exact hQ (by rw [hQB, hz, zero_mul])
  have hprod : ∀ z ∈ (univ : Set ℂ),
      ev (gcd P Q) z • (ev B z * F z - ev A z) = 0 := by
    intro z _
    have h := hglobal z
    conv at h => lhs; lhs; lhs; rw [hQB]
    conv at h => lhs; rhs; rw [hP]
    simp only [ev, Polynomial.map_mul, Polynomial.eval_mul] at h ⊢
    change _ * (_ * _ - _) = 0
    linear_combination h
  have hAB : ∀ z : ℂ, ev B z * F z - ev A z = 0 := by
    rcases (han (gcd P Q)).eq_zero_or_eq_zero_of_smul_eq_zero
      ((han B).mul hFa |>.sub (han A)) hprod isPreconnected_univ with hz | hz
    · have hp : (gcd P Q).map Complex.ofRealHom = 0 := by
        apply Polynomial.eq_zero_of_infinite_isRoot
        exact Set.infinite_univ.mono (fun z _ ↦ hz z (mem_univ z))
      exact (hD (Polynomial.map_injective Complex.ofRealHom Complex.ofReal_injective (by simpa using hp))).elim
    · exact fun z ↦ hz z (mem_univ z)
  have hcp : IsCoprime A B := (gcd_isUnit_iff_isRelPrime.mp hcop).isCoprime
  have hBne (z : ℂ) : ev B z ≠ 0 := by
    intro hz
    have ha : ev A z = 0 := by simpa [hz] using hAB z
    have hc := Polynomial.aeval_ne_zero_of_isCoprime
      ((Polynomial.isCoprime_map Complex.ofRealHom).mpr hcp) z
    simp [ev, Polynomial.aeval_def, hz, ha] at hc
  have hdeg : (B.map Complex.ofRealHom).natDegree = 0 := by
    by_contra hn
    obtain ⟨z, hz⟩ := Complex.exists_root
      (Polynomial.natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hn))
    exact hBne z hz
  have hBconst : B = Polynomial.C (B.coeff 0) :=
    Polynomial.eq_C_of_natDegree_eq_zero (by simpa using hdeg)
  have hevB (z : ℂ) : ev B z = ((B.coeff 0 : ℝ) : ℂ) := by
    change (B.map Complex.ofRealHom).eval z = _
    conv_lhs => rw [hBconst]
    simp
  have hb : B.coeff 0 ≠ 0 := by
    have h := hBne 0
    rw [hevB] at h
    exact_mod_cast h
  refine ⟨Polynomial.C ((B.coeff 0)⁻¹) * A, ?_⟩
  intro z
  have h := hAB z
  rw [hevB] at h
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, map_inv₀]
  rw [← Polynomial.eval_map]
  have hbC : (B.coeff 0 : ℂ) ≠ 0 := by exact_mod_cast hb
  calc F z = (B.coeff 0 : ℂ)⁻¹ * ((B.coeff 0 : ℂ) * F z) := by rw [inv_mul_cancel_left₀ hbC]
       _ = _ := by rw [sub_eq_zero.mp h]; rfl

/-- Theorem 1.1: an entire function preserving all Liouville numbers
is a polynomial with real coefficients. No real-axis assumption is required. -/
theorem theorem_1_1 {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hpres : ∀ x : ℝ, Liouville x → ∃ y : ℝ, Liouville y ∧ F x = y) :
    ∃ P : Polynomial ℝ, ∀ z : ℂ, F z = P.eval₂ Complex.ofRealHom z := by
  have hr := real_on_axis_of_preserves_liouville hF.continuous hpres
  apply entire_polynomial_of_rational_real_restriction hF hr
  apply rationalOn_of_preserves_liouville isOpen_univ isPreconnected_univ
    Set.univ_nonempty (analytic_real_restriction hF)
  intro x _ hx
  obtain ⟨y, hy, he⟩ := hpres x hx
  simpa [he] using hy

end MahlerLean
