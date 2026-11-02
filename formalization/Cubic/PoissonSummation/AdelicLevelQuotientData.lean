import Cubic.PoissonSummation.AdelicQuotientMeasure

/-!
# The actual double quotient and its logarithm

First quotient the original adelic torus by its rational diagonal, then by the
image of the specified subgroup `K^{D₀}`. Both topology and measurable structure
are the standard quotient structures. The measure is the pushforward of the
already constructed counting-normalized rational quotient measure.

The codomain `Multiplicative ℝ` is the invariant cocharacter line in coordinate
`u v₀`, with `v₀=(-1,-1)`. No isomorphism or measure formula is assumed here.
-/

noncomputable section

namespace Cubic.PoissonSummation.AdelicLevelQuotient

open MeasureTheory
open AdelicRationalCharacter AdelicCompactQuotient AdelicLevel
open scoped Cubic.QuadraticCorrespondence.RationalQuotientGroup
  Cubic.QuadraticCorrespondence.RegularFunctionTopology
  Cubic.QuadraticCorrespondence.QuotientLocalTopology
  ArchimedeanHaarData RestrictedProductHaar AdelicHeightZetaData

/-- The image of the actual compact level in the rational adelic quotient. -/
def quotientLevel : Subgroup AutomorphicQuotient :=
  level.map (QuotientGroup.mk' RationalAdelicEmbedding.diagonal.range)

/-- `T(ℚ)\T(𝔸)/K^{D₀}`, with the iterated quotient topology. -/
abbrev DoubleQuotient := AutomorphicQuotient ⧸ quotientLevel

def quotientProjection : AutomorphicQuotient →* DoubleQuotient :=
  QuotientGroup.mk' quotientLevel

def projection : AdelicData.Points →* DoubleQuotient :=
  quotientProjection.comp (QuotientGroup.mk' RationalAdelicEmbedding.diagonal.range)

theorem quotientLevel_le_ker : quotientLevel ≤ quotientCoordinate.ker := by
  rintro _ ⟨x, hx, rfl⟩
  exact coordinate_eq_one_of_mem_maximalCompact (level_le_maximalCompact hx)

/-- Descent of the original logarithm; it is not defined using a desired inverse. -/
def logarithm : DoubleQuotient →* Multiplicative ℝ :=
  QuotientGroup.lift quotientLevel quotientCoordinate quotientLevel_le_ker

def realCoordinate (x : DoubleQuotient) : ℝ := (logarithm x).toAdd

/-- The specified adelic radial section, followed by the double quotient. -/
def radial (u : ℝ) : DoubleQuotient := projection (AdelicData.radialSection u)

/-- Push forward the counting-normalized rational quotient measure through the level quotient. -/
def measure : Measure DoubleQuotient :=
  AdelicQuotientMeasure.quotientMeasure.map quotientProjection

end Cubic.PoissonSummation.AdelicLevelQuotient
