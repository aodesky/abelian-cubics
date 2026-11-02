import Cubic.SantensComparison.PicardLattices
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

noncomputable section

namespace Cubic.SantensComparison.ConeIntegral

open FanData MeasureTheory Set

theorem effective_cone (d : ℝ × ℝ) :
    d ∈ effectiveCone ↔ ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ d = (2*b,a-b) := by
  simp [effectiveCone, adelicProjection, Prod.smul_mk, smul_eq_mul, mul_comm, sub_eq_add_neg]

theorem dual_cone (z : ℝ × ℝ) : z ∈ dualCone ↔ 0 ≤ z.2 ∧ z.2 ≤ 2*z.1 := by
  constructor
  · intro h
    have hR := h (0,1) ((effective_cone _).mpr ⟨1,0, by norm_num⟩)
    have hH := h (2,-1) ((effective_cone _).mpr ⟨0,1, by norm_num⟩)
    simp only [mul_zero, mul_one, zero_add, mul_neg_one] at hR hH
    exact ⟨hR, by linarith⟩
  · rintro ⟨hq,hp⟩ d hd
    obtain ⟨a,b,ha,hb,rfl⟩ := (effective_cone d).mp hd
    change 0 ≤ z.1 * (2*b) + z.2 * (a-b)
    nlinarith [mul_nonneg ha hq, mul_nonneg hb (sub_nonneg.mpr hp)]

theorem measurable_dual_cone : MeasurableSet dualCone := by
  have he : dualCone = {z : ℝ × ℝ | 0 ≤ z.2 ∧ z.2 ≤ 2*z.1} :=
    Set.ext dual_cone
  rw [he]
  exact (measurableSet_le measurable_const measurable_snd).inter
    (measurableSet_le measurable_snd (measurable_const.mul measurable_fst))

private def integrand (z : ℝ × ℝ) : ℝ :=
  dualCone.indicator (fun z => Real.exp (-z.1)) z

private theorem slice (p : ℝ) :
    (fun q => integrand (p,q)) = (Icc 0 (2*p)).indicator (fun _ => Real.exp (-p)) := by
  ext q
  simp [integrand, Set.indicator, dual_cone]

private theorem slice_integrable (p : ℝ) : Integrable (fun q => integrand (p,q)) := by
  rw [slice]
  exact continuous_const.integrableOn_Icc.integrable_indicator measurableSet_Icc

private theorem slice_integral (p : ℝ) :
    (∫ q : ℝ, integrand (p,q)) =
      (Ici 0).indicator (fun p => 2 * (p * Real.exp (-p))) p := by
  rw [slice, integral_indicator measurableSet_Icc, setIntegral_const,
    Real.volume_real_Icc, sub_zero, smul_eq_mul]
  by_cases hp : 0 ≤ p
  · rw [max_eq_left (by linarith), Set.indicator_of_mem (show p ∈ Ici 0 from hp)]
    ring
  · rw [max_eq_right (by linarith), Set.indicator_of_notMem (show p ∉ Ici 0 from hp), zero_mul]

private theorem gamma_integrable : IntegrableOn (fun p : ℝ => p * Real.exp (-p)) (Ici 0) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  simpa only [show (2:ℝ)-1=1 by norm_num, Real.rpow_one, mul_comm] using
    Real.GammaIntegral_convergent (s := 2) (by norm_num)

private theorem integrand_integrable : Integrable integrand := by
  change Integrable integrand (volume.prod volume)
  apply (integrable_prod_iff ?_).mpr
  · refine ⟨Filter.Eventually.of_forall slice_integrable, ?_⟩
    have hn : ∀ z, ‖integrand z‖ = integrand z := by
      intro z
      apply Real.norm_of_nonneg
      exact Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) z
    simp_rw [hn, slice_integral]
    exact IntegrableOn.integrable_indicator (gamma_integrable.const_mul 2) measurableSet_Ici
  · exact ((Real.continuous_exp.comp continuous_fst.neg).measurable.indicator
      measurable_dual_cone).aestronglyMeasurable

/-- Fubini reduces the actual dual-cone integral, with lattice-normalized
Lebesgue measure, to `2∫₀∞ p exp(-p) dp`. -/
theorem cone_constant : theta = 2 := by
  unfold theta
  rw [← integral_indicator measurable_dual_cone]
  change (∫ z, integrand z) = 2
  rw [Measure.volume_eq_prod, integral_prod _ integrand_integrable]
  simp_rw [slice_integral]
  rw [integral_indicator measurableSet_Ici, integral_const_mul,
    integral_Ici_eq_integral_Ioi]
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := 1)
    (by norm_num) (by norm_num)
  norm_num at h
  rw [h]
  norm_num

end Cubic.SantensComparison.ConeIntegral
