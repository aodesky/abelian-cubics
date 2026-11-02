import Cubic.PoissonSummation.AdelicLevelQuotientData

/-!
# Concrete full target for `lemma:KprimeGroup`

The original logarithm must be a topological group isomorphism on the actual
double quotient. Its inverse is the paper's specified radial section, and the
pushforward of the actual quotient measure must be `du/6`. All data are fixed;
there are no arithmetic, isomorphism, or measure assumptions.
-/

namespace CubicTargets.PoissonSummation.KprimeGroup

open MeasureTheory Cubic.PoissonSummation
open AdelicLevelQuotient
open scoped Cubic.QuadraticCorrespondence.RationalQuotientGroup
  Cubic.QuadraticCorrespondence.RegularFunctionTopology
  Cubic.QuadraticCorrespondence.QuotientLocalTopology
  ArchimedeanHaarData RestrictedProductHaar AdelicHeightZetaData ENNReal

structure Claim : Prop where
  isomorphism : ∃ e : DoubleQuotient ≃ₜ* Multiplicative ℝ,
    (∀ x, e x = logarithm x) ∧
    (∀ u : ℝ, e.symm (Multiplicative.ofAdd u) = radial u)
  radial_logarithm : ∀ u : ℝ,
    AdelicData.logarithm (AdelicData.radialSection u) = (-u, -u)
  measure_pushforward : measure.map realCoordinate = (1 / 6 : ℝ≥0∞) • volume

end CubicTargets.PoissonSummation.KprimeGroup
