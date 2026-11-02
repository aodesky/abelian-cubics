import Cubic.SantensComparison.ToricFanData
import Cubic.SantensComparison.ToricMetricData

/-! Compatibility of the original local height with the resolved fan.
Linearity is proved on entire cones, rather than inferred from the values
on rays. The retained divisor identity also identifies the norm character
which appears in the local anticanonical measure. -/

noncomputable section

namespace Cubic.SantensComparison.ToricMetricGeometry

open ToricFanData ToricMetricData Cubic.ToricHeights
open Cubic.SurfaceGeometry.ResolutionData

def ambientCoordinates (v : ℝ × ℝ) : ℝ × ℝ :=
  ((2*v.1+v.2)/3,(v.1+2*v.2)/3)

/-- Rational piecewise-linear support data for a canonical toric metric.
The change to the original cocharacter coordinates is fixed by the proved
quotient-character parametrization of the torus. -/
structure CanonicalMetric (F : Fan) (φ : Support) : Prop where
  continuous : Continuous φ
  real : ∀ v, (φ v).im=0
  invariant : ∀ v, φ v.swap=φ v
  linear_on_cones : ∀ i, ∃ m : ℚ × ℚ, ∀ v ∈ F.cone i,
    φ (ambientCoordinates v)=((m.1:ℝ)*v.1+(m.2:ℝ)*v.2 : ℝ)

def paperCharacter (i : Fin 9) : ℚ × ℚ :=
  if i.val < 3 then (-1/3,-2/3) else if i.val < 6 then (0,0) else (-2/3,-1/3)

theorem paper_linear (i : Fin 9) (v : ℝ × ℝ) (hv : v ∈ paperFan.cone i) :
    paperSupport (ambientCoordinates v)=
      ((paperCharacter i).1*v.1+(paperCharacter i).2*v.2 : ℝ) := by
  have hr : -min 0 (min ((2*v.1+v.2)/3) ((v.1+2*v.2)/3)) =
      (paperCharacter i).1*v.1+(paperCharacter i).2*v.2 := by
    fin_cases i <;>
      norm_num [Fan.cone, Fan.realRay, Fan.next, paper_ray, paperFan, rays, detReal,
        paperCharacter] at hv ⊢ <;>
      (try simp only [min_def]) <;> (try split_ifs) <;>
      (repeat' constructor) <;> linarith
  apply Complex.ext
  · simpa [paperSupport, supportFunction, ambientCoordinates] using hr
  · simp [paperSupport, supportFunction]

theorem paper_metric : CanonicalMetric paperFan paperSupport where
  continuous := supportFunction_continuous (-1) 0
  real v := by simp [paperSupport, supportFunction]
  invariant := supportFunction_swap (-1) 0
  linear_on_cones i := ⟨paperCharacter i,paper_linear i⟩

theorem paper_divisor (i : Fin 9) :
    3*(paperSupport (ambientCoordinates (paperFan.realRay i))).re=pullbackThreeD0 i := by
  fin_cases i <;> norm_num [paperSupport, supportFunction, ambientCoordinates,
    Fan.realRay, paper_ray, paperFan, rays, pullbackThreeD0]

/-- On the open divisors and the real boundary face, the actual metric and
the actual logarithmic canonical divisor differ by the norm character. -/
theorem paper_log_anticanonical (i : Fin 9) (hi : boundary i=0 ∨ i=0) :
    (antiK i-boundary i : ℝ) =
      2*(paperSupport (ambientCoordinates (paperFan.realRay i))).re+
        FanData.pairing FanData.normCharacter i := by
  fin_cases i <;>
    norm_num [boundary, antiK, paperSupport, supportFunction, ambientCoordinates,
      Fan.realRay, paper_ray, paperFan, rays, FanData.pairing, FanData.normCharacter] at *

end Cubic.SantensComparison.ToricMetricGeometry
