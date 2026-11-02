import Cubic.SantensComparison.PadicCoordinateMeasure
import Cubic.SantensComparison.LogDifferentials
import Cubic.SantensComparison.PicardArtinFactors
import Cubic.ToricHeights.RamifiedLocalIntegrality

noncomputable section

namespace Cubic.SantensComparison.RamifiedGaugeVolume

open MeasureTheory Cubic.ToricHeights
open Cubic.QuadraticCorrespondence CyclotomicRamifiedField CyclotomicCoefficients
open scoped PadicCoordinateMeasure

/-- The actual coefficient-integrality conditions in the integral basis 1,ζ. -/
def coordinateLocus : Set (PadicCoordinateMeasure.Coordinates 3) :=
  {x | RamifiedLocalIntegrality.Conditions (x.1 : ℚ_[3]) (x.2 : ℚ_[3])}

theorem coordinate_locus : coordinateLocus =
    {x | PadicCoordinateMeasure.reduction 3 x =
      PadicCoordinateMeasure.reduction 3 (1,0)} := by
  ext x
  rw [Set.mem_setOf_eq, PadicCoordinateMeasure.reduction_eq_iff]
  change RamifiedLocalIntegrality.Conditions (x.1 : ℚ_[3]) (x.2 : ℚ_[3]) ↔ _
  rw [RamifiedLocalIntegrality.conditions_iff_coordinate_congruences]
  simp only [sub_zero]
  constructor
  · rintro ⟨c,d,hc,hd⟩
    constructor
    · refine ⟨c, ?_⟩
      apply Subtype.ext
      change (x.1 : ℚ_[3])-1=3*(c:ℚ_[3])
      linear_combination hc
    · exact ⟨d, Subtype.ext hd⟩
  · rintro ⟨⟨c,hc⟩,⟨d,hd⟩⟩
    refine ⟨c,d,?_,?_⟩
    · have hh := congrArg (fun a : ℤ_[3] => (a : ℚ_[3])) hc
      change (x.1 : ℚ_[3])-1=3*(c:ℚ_[3]) at hh
      linear_combination hh
    · exact congrArg (fun a : ℤ_[3] => (a : ℚ_[3])) hd

theorem measurable_coordinate_locus : MeasurableSet coordinateLocus := by
  rw [coordinate_locus]
  exact PadicCoordinateMeasure.measurable_fiber 3 (1,0)

theorem coordinate_volume : (PadicCoordinateMeasure.measure 3).real coordinateLocus = 1/9 := by
  rw [coordinate_locus, PadicCoordinateMeasure.fiber_mass]
  norm_num

theorem norm_on_locus (x : PadicCoordinateMeasure.Coordinates 3) (hx : x ∈ coordinateLocus) :
    ‖linear (x.1 : ℚ_[3]) (x.2 : ℚ_[3])‖ ^ 2 = 1 := by
  have hr : PadicInt.toZMod x.1 = 1 ∧ PadicInt.toZMod x.2 = 0 := by
    rw [coordinate_locus] at hx
    change (PadicInt.toZMod x.1,PadicInt.toZMod x.2) = _ at hx
    simpa [PadicCoordinateMeasure.reduction] using Prod.mk.inj hx
  have hn : PadicInt.toZMod (normForm x.1 x.2) = (1 : ZMod 3) := by
    simp [normForm, hr.1, hr.2]
  have hu : ‖normForm x.1 x.2‖ = 1 := by
    by_contra hh
    have hlt : ‖normForm x.1 x.2‖ < 1 := lt_of_le_of_ne (PadicInt.norm_le_one _) hh
    have hz : PadicInt.toZMod (normForm x.1 x.2) = (0 : ZMod 3) := by
      rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal,
        PadicInt.mem_nonunits]
      exact hlt
    rw [hn] at hz
    exact one_ne_zero hz
  rw [← RamifiedLocalIntegrality.norm_normForm]
  exact hu

/-- Absolute coefficient of the logarithmic wedge in the basis du∧dv.
`LogDifferentials.cyclotomic_log_wedge` identifies this with the actual
character differential, and the squared norm is the absolute value of n. -/
def gaugeDensity (x : PadicCoordinateMeasure.Coordinates 3) : ℝ :=
  ‖2*zeta+1‖ / ‖linear (x.1 : ℚ_[3]) (x.2 : ℚ_[3])‖^2

def gaugeVolume : ℝ :=
  ∫ x in coordinateLocus, gaugeDensity x ∂PadicCoordinateMeasure.measure 3

theorem gauge_volume : gaugeVolume = 1/(9*Real.sqrt 3) := by
  unfold gaugeVolume
  calc
    _ = ∫ _x in coordinateLocus, (1/Real.sqrt 3 : ℝ) ∂PadicCoordinateMeasure.measure 3 := by
      apply setIntegral_congr_fun measurable_coordinate_locus
      intro x hx
      rw [gaugeDensity, norm_on_locus x hx, div_one, LogDifferentials.ramified_differential_norm]
    _ = _ := by
      rw [setIntegral_const, coordinate_volume, smul_eq_mul]
      ring

def normalizedVolume : ℝ :=
  (PicardArtinFactors.ramifiedPolynomial ((3 : ℂ)^(-1 : ℂ))).re * gaugeVolume

theorem normalized_volume : normalizedVolume = 2/(27*Real.sqrt 3) := by
  rw [normalizedVolume, PicardArtinFactors.ramified_polynomial,
    Complex.cpow_neg_one, gauge_volume]
  norm_num
  ring

end Cubic.SantensComparison.RamifiedGaugeVolume
