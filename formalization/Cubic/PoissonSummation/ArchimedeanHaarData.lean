import Cubic.PoissonSummation.AdelicFourierComponents

/-!
# The original archimedean Fourier integral and its measure convention

The measure convention is the paper's: pushforward under the original
logarithmic coordinate is Lebesgue measure, so the lattice `ℤ v₀` has covolume
one. Existence and uniqueness of this Haar measure are proved in `ArchimedeanHaar`.
The height and automorphic character are the independently constructed ones.
-/

noncomputable section

namespace Cubic.PoissonSummation.ArchimedeanHaarData

open MeasureTheory Cubic.QuadraticCorrespondence
open scoped RegularFunctionTopology RationalQuotientGroup QuotientLocalTopology

abbrev Points := Cubic.ToricHeights.ArchimedeanQuotientLogarithm.Points

scoped instance : MeasurableSpace Points := borel Points
scoped instance : BorelSpace Points := ⟨rfl⟩

/-- The paper's Haar convention on the original real torus. -/
def NormalizedHaar (μ : Measure Points) : Prop :=
  μ.IsHaarMeasure ∧
    μ.map Cubic.ToricHeights.ArchimedeanQuotientLogarithm.coordinate = volume

/-- Restrict the adelic height and the inverse descended automorphic character
to the original real torus. The archimedean integrality cutoff is one. -/
def integrand (s₀ σ : ℂ) (t : ℝ) (x : Points) : ℂ :=
  AdelicData.inverseHeight s₀ σ (AdelicData.includeInfinite x) *
    ((AdelicRationalCharacter.automorphicCharacter t
      (QuotientGroup.mk (AdelicData.includeInfinite x)) : Circle) : ℂ)⁻¹

/-- Actual Bochner integral on the original real torus, for a specified measure. -/
def fourier (μ : Measure Points) (s₀ σ : ℂ) (t : ℝ) : ℂ :=
  ∫ x, integrand s₀ σ t x ∂μ

end Cubic.PoissonSummation.ArchimedeanHaarData
