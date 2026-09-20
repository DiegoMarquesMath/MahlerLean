import MahlerLean.UniformSublevelGlobal
import MahlerLean.SublevelIntervals

open Set MeasureTheory

noncomputable section
namespace MahlerLean

/-- Local interval decomposition, with a common bound for all jet orders. -/
theorem jetLinearCombo_interval_cover
    {N : ℕ} (φ : Fin N → ℝ → ℝ) (c : EuclideanSpace ℝ (Fin N))
    {U : Set ℝ} (hφ : ∀ j, AnalyticOnNhd ℝ (φ j) U)
    {a b eps lam : ℝ} (k : Fin N) (hI : Icc a b ⊆ U)
    (hlam : 0 < lam) (hepslam : eps < lam)
    (hlow : ∀ x ∈ Icc a b, lam ≤ |jetApply φ c k x|) :
    ∃ t : Finset (Set ℝ), t.card ≤ 4 * (N - 1) + 1 ∧
      (∀ E ∈ t, E.OrdConnected) ∧
      (∀ x, (x ∈ Icc a b ∧ ‖jetLinearCombo φ c x‖ ≤ eps) ↔
        ∃ E ∈ t, x ∈ E) := by
  classical
  by_cases hk : k.val = 0
  · have hempty := jetLinearCombo_sublevel_eq_empty_of_zero_order
      φ c hφ k hk hI hepslam hlow
    refine ⟨∅, by simp, by simp, ?_⟩
    intro x
    have hx : ¬ (x ∈ Icc a b ∧ ‖jetLinearCombo φ c x‖ ≤ eps) := by
      intro hx
      have hm : x ∈ ({y | y ∈ Icc a b ∧ ‖jetLinearCombo φ c y‖ ≤ eps} : Set ℝ) := hx
      rw [hempty] at hm
      exact hm
    simp [hx]
  · obtain ⟨hcont, _⟩ := analyticFamily_linearCombo_smooth φ c hφ hI
    have hder : ∀ x ∈ Icc a b,
        lam ≤ |iteratedDeriv k.val (jetLinearCombo φ c) x| := by
      intro x hx
      rw [iteratedDeriv_jetLinearCombo_eq_jetApply φ c hφ (hI hx) k]
      exact hlow x hx
    obtain ⟨t,ht,hconn,hcov⟩ := sublevel_interval_cover_of_derivative_bound
      (eps := eps) (Nat.pos_of_ne_zero hk) hcont hlam hder
    refine ⟨t, ?_, hconn, hcov⟩
    have := k.isLt
    omega

/-- Uniform interval complexity of analytic sublevels under Wronskian
nondegeneracy. The interval pieces may overlap; their union is exact. -/
theorem exists_uniform_analytic_sublevel_interval_cover
    {N : ℕ} (hN : 0 < N) (φ : Fin N → ℝ → ℝ)
    {U : Set ℝ} (hU : IsOpen U) (hφ : ∀ j, AnalyticOnNhd ℝ (φ j) U)
    {A B : ℝ} (hJU : Icc A B ⊆ U)
    (hW : ∀ x ∈ Icc A B, wronskian φ x ≠ 0) :
    ∃ lam : ℝ, 0 < lam ∧ ∃ R : ℕ,
      ∀ c : EuclideanSpace ℝ (Fin N), ‖c‖ = 1 →
      ∀ eps : ℝ, eps < lam →
      ∃ t : Finset (Set ℝ), t.card ≤ R ∧
        (∀ E ∈ t, E.OrdConnected) ∧
        (∀ x, (x ∈ Icc A B ∧ ‖jetLinearCombo φ c x‖ ≤ eps) ↔
          ∃ E ∈ t, x ∈ E) := by
  classical
  obtain ⟨eta, heta, k, C, a, b, _hC, _hcenter, hIU, hbound, t, hcover⟩ :=
    exists_finite_uniform_jet_interval_cover_of_analytic
      hN φ hU hφ isCompact_Icc hJU hW
  refine ⟨eta / 2, by linarith, t.card * (4 * (N - 1) + 1), ?_⟩
  intro c hc eps heps
  let s := t.filter (fun p => c ∈ C p)
  have hlocal : ∀ p : {p // p ∈ s},
      ∃ v : Finset (Set ℝ), v.card ≤ 4 * (N - 1) + 1 ∧
        (∀ E ∈ v, E.OrdConnected) ∧
        (∀ x, (x ∈ Icc (a p.val) (b p.val) ∧ ‖jetLinearCombo φ c x‖ ≤ eps) ↔
          ∃ E ∈ v, x ∈ E) := by
    intro p
    exact jetLinearCombo_interval_cover φ c hφ (k p.val) (hIU p.val)
      (by linarith) heps (hbound p.val c (Finset.mem_filter.mp p.property).2)
  choose v hvcard hvconn hvcov using hlocal
  let all : Finset (Set ℝ) := Finset.univ.biUnion v
  let clipped : Finset (Set ℝ) := all.image (fun E => E ∩ Icc A B)
  have hallcard : all.card ≤ s.card * (4 * (N - 1) + 1) := by
    calc
      all.card ≤ ∑ p : {p // p ∈ s}, (v p).card := by simpa [all] using (Finset.card_biUnion_le (s := Finset.univ) (t := v))
      _ ≤ ∑ _p : {p // p ∈ s}, (4 * (N - 1) + 1) :=
        Finset.sum_le_sum (fun p _ => hvcard p)
      _ = s.card * (4 * (N - 1) + 1) := by simp
  refine ⟨clipped, ?_, ?_, ?_⟩
  · exact (Finset.card_image_le).trans (hallcard.trans
      (Nat.mul_le_mul_right _ (Finset.card_filter_le _ _)))
  · intro E hE
    obtain ⟨F,hF,rfl⟩ := Finset.mem_image.mp hE
    obtain ⟨p,_,hp⟩ := Finset.mem_biUnion.mp hF
    exact (hvconn p F hp).inter ordConnected_Icc
  · intro x
    constructor
    · intro hx
      have hq : (c,x) ∈ coefficientSourceProduct N (Icc A B) :=
        (mem_coefficientSourceProduct (K := Icc A B) (c,x)).mpr ⟨hc,hx.1⟩
      obtain ⟨p,hpt,hcp,hxp⟩ := hcover (c,x) hq
      have hps : p ∈ s := Finset.mem_filter.mpr ⟨hpt,hcp⟩
      obtain ⟨E,hE,hxE⟩ := (hvcov ⟨p,hps⟩ x).mp ⟨⟨hxp.1.le,hxp.2.le⟩,hx.2⟩
      have hall : E ∈ all := Finset.mem_biUnion.mpr ⟨⟨p,hps⟩,Finset.mem_univ _,hE⟩
      exact ⟨E ∩ Icc A B, Finset.mem_image.mpr ⟨E,hall,rfl⟩,hxE,hx.1⟩
    · rintro ⟨E,hE,hxE⟩
      obtain ⟨F,hF,rfl⟩ := Finset.mem_image.mp hE
      obtain ⟨p,_,hp⟩ := Finset.mem_biUnion.mp hF
      have hx := (hvcov p x).mpr ⟨F,hp,hxE.1⟩
      exact ⟨hxE.2,hx.2⟩

end MahlerLean
