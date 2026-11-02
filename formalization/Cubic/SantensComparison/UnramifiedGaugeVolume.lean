import Cubic.SantensComparison.NormalizedLocalVolumes
import Cubic.SantensComparison.PicardArtinFactors
import Cubic.Counting.AsymptoticConstantsData

/-! Haar representatives of the good-reduction gauge measures. Their compact
masses are the reciprocal Artin factors, the normalization of Santens Lemma
4.27. The identification with Construction 4.25 is a literature specialization,
not an assumed value for the integral over the coefficient-integrality locus.
That integral is evaluated below using the proved norm moments. -/

noncomputable section

namespace Cubic.SantensComparison.UnramifiedGaugeVolume

open MeasureTheory LocalVolumeData NormalizedLocalVolumes PicardArtinFactors
open Cubic.ToricHeights Cubic.PoissonSummation.FiniteEulerProduct
open Cubic.Counting.AsymptoticConstantsData
open scoped SplitLocalModel InertLocalModel

local instance primeFact (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩
local instance inertFact (p : InertPrimes) : Fact ((p.1 : ℕ) % 3 = 2) := ⟨p.2⟩

local instance unitsSecondCountable {R : Type*} [Monoid R] [TopologicalSpace R]
    [SecondCountableTopology R] : SecondCountableTopology Rˣ := by
  letI : SecondCountableTopology Rᵐᵒᵖ :=
    (MulOpposite.opHomeomorph : R ≃ₜ Rᵐᵒᵖ).symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

def splitScale (p : SplitPrimes) : ℝ := (splitPolynomial ((p.1 : ℂ)^(-1 : ℂ))).re
def inertScale (p : InertPrimes) : ℝ := (inertPolynomial ((p.1 : ℂ)^(-1 : ℂ))).re

def splitMeasure (p : SplitPrimes) : Measure (SplitLocalModel.Points p.1) :=
  ENNReal.ofReal (splitScale p) • SplitLocalModel.measure p.1

def inertMeasure (p : InertPrimes) : Measure (InertLocalModel.Points p.1) :=
  ENNReal.ofReal (inertScale p) • InertLocalModel.measure p.1

def splitVolume (p : SplitPrimes) : ℝ := splitScale p * ∫ x, splitWeight p x ∂splitMeasure p
def inertVolume (p : InertPrimes) : ℝ := inertScale p * ∫ x, inertWeight p x ∂inertMeasure p

theorem split_scale (p : SplitPrimes) : splitScale p = (1-1/(p.1:ℝ))^2 := by
  unfold splitScale
  rw [split_polynomial, Complex.cpow_neg_one]
  have h : (1-(p.1:ℂ)⁻¹)^2 = (((1-1/(p.1:ℝ))^2 : ℝ) : ℂ) := by
    push_cast
    simp [one_div]
  rw [h, Complex.ofReal_re]

theorem inert_scale (p : InertPrimes) : inertScale p = 1-1/(p.1:ℝ)^2 := by
  unfold inertScale
  rw [inert_polynomial, Complex.cpow_neg_one]
  have h : 1-(p.1:ℂ)⁻¹^2 = ((1-1/(p.1:ℝ)^2 : ℝ) : ℂ) := by
    push_cast
    simp [one_div, inv_pow]
  rw [h, Complex.ofReal_re]

theorem split_scale_pos (p : SplitPrimes) : 0 < splitScale p := by
  rw [split_scale]
  have hp : (1:ℝ) < p.1 := by exact_mod_cast p.1.2.one_lt
  exact sq_pos_of_pos (sub_pos.mpr (by simpa only [one_div] using inv_lt_one_of_one_lt₀ hp))

theorem inert_scale_pos (p : InertPrimes) : 0 < inertScale p := by
  rw [inert_scale]
  have hp : (1:ℝ) < p.1 := by exact_mod_cast p.1.2.one_lt
  exact sub_pos.mpr (by simpa only [one_div] using
    inv_lt_one_of_one_lt₀ (by nlinarith : (1:ℝ) < (p.1:ℝ)^2))

theorem split_compact_mass (p : SplitPrimes) :
    (splitMeasure p).real (SplitLocalModel.compactUnits p.1) = splitScale p := by
  simp [splitMeasure, Measure.real, SplitLocalModel.measure_compactUnits,
    ENNReal.toReal_ofReal (split_scale_pos p).le]

theorem inert_compact_mass (p : InertPrimes) :
    (inertMeasure p).real (InertLocalModel.compactUnits p.1) = inertScale p := by
  simp [inertMeasure, Measure.real, InertLocalModel.measure_compactUnits,
    ENNReal.toReal_ofReal (inert_scale_pos p).le]

/-- Haar uniqueness makes the good-reduction compact-volume statement a
measure identity; it does not just compare the values of our test integral. -/
theorem split_gauge_unique (p : SplitPrimes) (μ : Measure (SplitLocalModel.Points p.1))
    [SigmaFinite μ] [μ.IsMulLeftInvariant]
    (hμ : μ (SplitLocalModel.compactUnits p.1) = ENNReal.ofReal (splitScale p)) :
    μ = splitMeasure p := by
  rw [Measure.haarMeasure_unique μ (SplitLocalModel.compactNeighborhood p.1)]
  change μ (SplitLocalModel.compactUnits p.1) • SplitLocalModel.measure p.1 = _
  rw [hμ]
  rfl

theorem inert_gauge_unique (p : InertPrimes) (μ : Measure (InertLocalModel.Points p.1))
    [SigmaFinite μ] [μ.IsMulLeftInvariant]
    (hμ : μ (InertLocalModel.compactUnits p.1) = ENNReal.ofReal (inertScale p)) :
    μ = inertMeasure p := by
  rw [Measure.haarMeasure_unique μ (InertLocalModel.compactNeighborhood p.1)]
  change μ (InertLocalModel.compactUnits p.1) • InertLocalModel.measure p.1 = _
  rw [hμ]
  rfl

theorem split_volume (p : SplitPrimes) : splitVolume p = originalSplitFactor p := by
  rw [splitVolume, splitMeasure, integral_smul_measure, ENNReal.toReal_ofReal (split_scale_pos p).le]
  change splitScale p * (splitScale p * splitMoment p) = _
  rw [(split_moment p).2, split_scale, originalSplitFactor]
  have hp : (1:ℝ) < p.1 := by exact_mod_cast p.1.2.one_lt
  have hp₀ : (p.1:ℝ) ≠ 0 := by linarith
  have hsub : 1-1/(p.1:ℝ) ≠ 0 := (sub_pos.mpr (by
    simpa only [one_div] using inv_lt_one_of_one_lt₀ hp)).ne'
  field_simp
  ring

theorem inert_volume (p : InertPrimes) : inertVolume p = originalInertFactor p := by
  rw [inertVolume, inertMeasure, integral_smul_measure, ENNReal.toReal_ofReal (inert_scale_pos p).le]
  change inertScale p * (inertScale p * inertMoment p) = _
  rw [(inert_moment p).2, ← inert_scale, mul_inv_cancel₀ (inert_scale_pos p).ne', mul_one]
  exact inert_scale p

end Cubic.SantensComparison.UnramifiedGaugeVolume
