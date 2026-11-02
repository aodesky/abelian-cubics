import Cubic.ToricHeights.AffinePointComparison
import Cubic.BoxAsymptotic.HeckeModulus
import Cubic.PoissonSummation.AdelicHeightZetaData

/-! The original affine integral points, primary Eisenstein integers of cube
norm, and actual ideals prime to three. These definitions contain no
parametrization or counting assertion. -/

noncomputable section

namespace Cubic.Introduction.EisensteinPointData

open Cubic.QuadraticCorrespondence CyclotomicField
open Cubic.ToricHeights
open Cubic.PoissonSummation.CyclotomicIntegerUnits
open Cubic.BoxAsymptotic.PrimaryGenerator

abbrev IntegralTorus :=
  {P : AffinePointComparison.TorusPoints // AffineInvariantRing.IntegralPoint P}

abbrev IntegralAffine :=
  {P : AffinePointComparison.ChartPoints // AffineChartInvariants.IsD0Integral P}

abbrev PrimaryCubes :=
  {β : Integers // IsPrimary β ∧ ∃ M : ℕ, Algebra.norm ℚ (β : E) = (M : ℚ) ^ 3}

abbrev CubeIdeals :=
  {I : Ideal Integers // ¬ 3 ∣ Ideal.absNorm I ∧ ∃ M : ℕ, Ideal.absNorm I = M ^ 3}

/-- The resolvent used to pass from the quotient parameter to a cube-norm element. -/
def resolvent (α : E) : E := algebraMap ℚ E (Algebra.norm ℚ α) * α

def pointResolvent (P : AffinePointComparison.TorusPoints) : E :=
  resolvent (RationalCoefficientFormula.parameterEquiv P : E)

def pointHeight (P : IntegralTorus) : ℝ :=
  (Cubic.PoissonSummation.AdelicHeightZetaData.height 1 0
    (Cubic.PoissonSummation.RationalAdelicEmbedding.diagonal P.1)).re

end Cubic.Introduction.EisensteinPointData
