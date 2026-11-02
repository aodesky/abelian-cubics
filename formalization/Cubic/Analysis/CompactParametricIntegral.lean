import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Differentiation under an integral on a fixed compact interval. Continuity
of the displayed derivative supplies its local integrable majorant. -/

noncomputable section

namespace Cubic.Analysis.CompactParametricIntegral

open Set MeasureTheory Filter
open scoped Topology

theorem hasDerivAt_interval {F F' : ℝ × ℝ → ℂ}
    (hF : Continuous F) (hF' : Continuous F')
    (hd : ∀ x y, HasDerivAt (fun u => F (u, y)) (F' (x, y)) x)
    {a b : ℝ} (hab : a ≤ b) (x₀ : ℝ) :
    HasDerivAt (fun x => ∫ y in a..b, F (x, y)) (∫ y in a..b, F' (x₀, y)) x₀ := by
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod isCompact_Icc).bddAbove_image
    (K := Icc (x₀ - 1) (x₀ + 1) ×ˢ Icc a b) hF'.norm.continuousOn
  have hs : Ioo (x₀ - 1) (x₀ + 1) ∈ 𝓝 x₀ := Ioo_mem_nhds (by linarith) (by linarith)
  have hFmeas : ∀ᶠ x in 𝓝 x₀,
      AEStronglyMeasurable (fun y => F (x, y)) (volume.restrict (Icc a b)) :=
    Eventually.of_forall fun x =>
      (hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hFi : IntegrableOn (fun y => F (x₀, y)) (Icc a b) :=
    (hF.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact
      isCompact_Icc
  have hF'meas : AEStronglyMeasurable (fun y => F' (x₀, y))
      (volume.restrict (Icc a b)) :=
    (hF'.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hb : ∀ᵐ y ∂volume.restrict (Icc a b), ∀ x ∈ Ioo (x₀ - 1) (x₀ + 1),
      ‖F' (x, y)‖ ≤ M := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy x hx
    exact hM (mem_image_of_mem _ ⟨⟨hx.1.le, hx.2.le⟩, hy⟩)
  have hdi : ∀ᵐ y ∂volume.restrict (Icc a b), ∀ x ∈ Ioo (x₀ - 1) (x₀ + 1),
      HasDerivAt (fun u => F (u, y)) (F' (x, y)) x :=
    Eventually.of_forall fun y x _ => hd x y
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hFmeas hFi hF'meas hb
    (integrableOn_const isCompact_Icc.measure_ne_top) hdi).2
  simpa only [intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc] using h

end Cubic.Analysis.CompactParametricIntegral
