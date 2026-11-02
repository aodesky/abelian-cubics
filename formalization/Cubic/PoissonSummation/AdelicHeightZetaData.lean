import Cubic.PoissonSummation.RestrictedProductHaar
import Cubic.PoissonSummation.ArchimedeanHaar
import Cubic.PoissonSummation.RationalAdelicEmbedding

/-!
# Concrete data for the height convergence lemma

The cutoff is defined by the original three local invariants at every finite
prime. The height and rational diagonal are the independently constructed
objects. The measure is the product of the archimedean Haar measure and the
finite restricted-product Haar measure, normalized on the maximal compacts.
No convergence assertion is assumed by these definitions.
-/

noncomputable section

namespace Cubic.PoissonSummation.AdelicHeightZetaData

open MeasureTheory
open Cubic.QuadraticCorrespondence
open QuotientFiniteFourierProduct
open scoped RegularFunctionTopology RationalQuotientGroup QuotientLocalTopology
  ArchimedeanHaarData RestrictedProductHaar

abbrev Points := AdelicData.Points
abbrev RationalPoints := RationalAdelicEmbedding.Points

/-- Finite Haar measure gives mass one to the product of the maximal compacts. -/
def finiteMeasure : Measure FiniteAdelicData.Points :=
  RestrictedProductHaar.measure (fun p => (family p).Carrier)
    (fun p => (family p).maxCompact) (fun p => (family p).compact)

/-- The paper's adelic Haar normalization, before quotienting by rational points. -/
def measure : Measure Points := ArchimedeanHaar.measure.prod finiteMeasure

def finiteIntegralLocus : Set FiniteAdelicData.Points :=
  {x | ∀ p, x p ∈ (family p).integralLocus}

def integralLocus : Set Points := {x | x.2 ∈ finiteIntegralLocus}

/-- The actual inverse height multiplied by its original integral-locus indicator. -/
def cutoffHeight (s₀ σ : ℂ) : Points → ℂ :=
  integralLocus.indicator (AdelicData.inverseHeight s₀ σ)

/-- The genuine rational-point summand translated by the specified real section. -/
def periodizationTerm (s₀ σ : ℂ) (γ : RationalPoints) (u : ℝ) : ℂ :=
  cutoffHeight s₀ σ (RationalAdelicEmbedding.diagonal γ * AdelicData.radialSection u)

def periodization (s₀ σ : ℂ) (u : ℝ) : ℂ := ∑' γ, periodizationTerm s₀ σ γ u

abbrev IntegralRationalPoints :=
  {γ : RationalPoints // RationalAdelicEmbedding.diagonal γ ∈ integralLocus}

/-- Positive-parameter height, defined from the original local height pairing. -/
def height (s₀ σ : ℂ) (x : Points) : ℂ := AdelicData.inverseHeight (-s₀) (-σ) x

/-- The original reciprocal-height summand, independently of any periodization formula. -/
def zetaTerm (s₀ σ : ℂ) (γ : IntegralRationalPoints) : ℂ :=
  (height s₀ σ (RationalAdelicEmbedding.diagonal γ.1))⁻¹

def heightZeta (s₀ σ : ℂ) : ℂ := ∑' γ, zetaTerm s₀ σ γ

end Cubic.PoissonSummation.AdelicHeightZetaData
