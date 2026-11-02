import Cubic.BoxAsymptotic.SmoothTransformData
import Cubic.BoxAsymptotic.ZeroModeLaurent

/-! The residue in `lem:smooth`, including the normalized angular measure.
This identifies the main integral before any contour shift is asserted. -/

noncomputable section

namespace Cubic.BoxAsymptotic.SmoothZeroResidue

open MeasureTheory Set Complex Filter Asymptotics
open Cubic.BoxAsymptotic.SmoothTransformData Cubic.BoxAsymptotic.ZeroModeData
open CubicTargets.BoxAsymptotic
open scoped Topology

variable {w : ℝ × ℝ → ℝ} {a b : ℝ}

theorem coefficient_zero (x : ℝ) :
    angularCoefficient w 0 x =
      ((∫ θ in (0 : ℝ)..2 * Real.pi, w (x, θ)) / (2 * Real.pi) : ℝ) := by
  simp only [angularCoefficient, neg_zero, AngularSeriesData.character_zero, mul_one,
    intervalIntegral.integral_ofReal]
  push_cast
  ring

/-- The two Mellin values occurring in the residue are the mass and logarithmic mass. -/
theorem residue_integral (hw : Continuous w) (ha : 0 < a)
    (hs : Function.support w ⊆ {p | a ≤ p.1 ∧ p.1 ≤ b}) :
    (aStar : ℂ) * deriv (transform w 0) 1 + (b₀ : ℂ) * transform w 0 1 =
      (((∫ x in Ioi (0 : ℝ), ∫ θ in (0 : ℝ)..2 * Real.pi,
          w (x, θ) * (aStar * Real.log x + b₀) / (2 * Real.pi)) : ℝ) : ℂ) := by
  have hc := angularCoefficient_continuous hw 0
  have hsup := angularCoefficient_support hs 0
  have hi := Cubic.Analysis.CompactMellin.integrable hc ha hsup
  have hlog := Cubic.Analysis.CompactMellin.log_integrable hc ha hsup
  rw [(transform_hasDerivAt hw ha hs 0 1).deriv]
  change (aStar : ℂ) * mellin (fun x => Real.log x • angularCoefficient w 0 x) 1 +
    (b₀ : ℂ) * mellin (angularCoefficient w 0) 1 = _
  rw [Cubic.Analysis.CompactMellin.at_one, Cubic.Analysis.CompactMellin.at_one]
  simp only [Complex.real_smul]
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add (hlog.const_mul _) (hi.const_mul _), ← integral_complex_ofReal]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x _
  dsimp only
  rw [coefficient_zero (w := w) x, intervalIntegral.integral_div,
    intervalIntegral.integral_mul_const]
  push_cast
  ring

/-- The simple-pole coefficient of the weighted zero mode. -/
def residue (w : ℝ × ℝ → ℝ) : ℂ :=
  (aStar : ℂ) * deriv (transform w 0) 1 + (b₀ : ℂ) * transform w 0 1

theorem weighted_laurent (hw : Continuous w) (ha : 0 < a)
    (hs : Function.support w ⊆ {p | a ≤ p.1 ∧ p.1 ≤ b}) :
    (fun s => continuation s * transform w 0 s -
      ((aStar : ℂ) * transform w 0 1) / (s - 1) ^ 2 - residue w / (s - 1))
      =O[𝓝[≠] (1 : ℂ)] (fun _ => (1 : ℂ)) := by
  have hT := (transform_entire hw ha hs 0).analyticAt 1
  have hA := ZeroModeLaurent.numerator_analytic.fun_mul hT
  have he : (fun s => continuation s * transform w 0 s) =ᶠ[𝓝[≠] (1 : ℂ)]
      (fun s => (numerator s * transform w 0 s) / (s - 1) ^ 2) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [ZeroModeLaurent.quotient hs]
    ring
  have hd : deriv (fun s => numerator s * transform w 0 s) 1 = residue w := by
    rw [(ZeroModeLaurent.numerator_analytic.differentiableAt.hasDerivAt.fun_mul
      hT.differentiableAt.hasDerivAt).deriv, ZeroModeLaurent.numerator_one,
      ZeroModeLaurent.derivative_real]
    simp only [residue]
    ring
  simpa only [hd, ZeroModeLaurent.numerator_one] using
    Cubic.PoissonSummation.AnalyticLaurent.laurent_of_analytic_numerator hA he

end Cubic.BoxAsymptotic.SmoothZeroResidue
