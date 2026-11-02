import Cubic.ToricHeights.IntegralPolynomialData

/-!
# Full concrete target for `lemma:rootVsToric`

All points, coefficients and heights are independently defined on the
original descended quotient and its all-functions integral locus. Reality of
the adelic height and agreement with the original characteristic polynomial
are retained. The comparability assertion has the explicit witnesses 1 and 2,
a stronger quantitative form of the paper's uniform `asymp` statement.
-/

namespace CubicTargets.ToricHeights.RootVsToric

open Cubic.ToricHeights.IntegralPolynomialData Cubic.PoissonSummation
open Cubic.QuadraticCorrespondence.DescendedCoefficients Polynomial

structure PointStatement (P : Points) : Prop where
  descended : (polynomial P).map (Int.castRingHom ℚ) = characteristicPolynomial P.val
  height_real : AdelicHeightZetaData.height 1 0 (RationalAdelicEmbedding.diagonal P.val) =
    (toricHeight P : ℂ)
  linear_nonpos : linear P ≤ 0
  root_square : rootHeight P ^ 2 = -(linear P : ℝ)
  toric_square : toricHeight P ^ 2 = 1 + 3 * rootHeight P ^ 2
  bounds : ∀ B : ℝ, 0 ≤ B →
    (rootHeight P ≤ B ↔ toricHeight P ≤ Real.sqrt (1 + 3 * B ^ 2))
  comparison : max 1 (rootHeight P) ≤ toricHeight P ∧
    toricHeight P ≤ 2 * max 1 (rootHeight P)
  zero_iff : rootHeight P = 0 ↔ polynomial P = X ^ 3 - X ^ 2
  zero_height : rootHeight P = 0 → toricHeight P = 1

def Claim : Prop := ∀ P : Points, PointStatement P

end CubicTargets.ToricHeights.RootVsToric
