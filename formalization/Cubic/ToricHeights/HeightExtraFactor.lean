import CubicTargets.ToricHeights.HeightExtraFactor
import Cubic.ToricHeights.LocalHeightFormula
import Cubic.ToricHeights.FiniteWeightHeight
import Cubic.PoissonSummation.IntegralPointComparison

/-!
# Proof of `eqn:heightExtraFactor`

Following the paper: `eqn:localHeight` gives each local factor; at a `D₀`-integral point
every finite factor is one (`FiniteWeightHeight.local_height_one`, which supplies the
argument the paper leaves implicit: `z±` are integral, being roots of a monic quadratic
with integral coefficients),
and at the complex place `z₋ = conj z₊`, so the four-term maximum of `eqn:localHeight`
reduces to the displayed three-term maximum with `[E:ℚ] = 2`.
-/

noncomputable section

namespace Cubic.ToricHeights.HeightExtraFactor

open Cubic.QuadraticCorrespondence CyclotomicTorusGalois DescendedCoefficients
open Cubic.PoissonSummation RationalAdelicEmbedding
open CubicTargets.ToricHeights.LocalHeightFormula CubicTargets.ToricHeights.HeightExtraFactor

/-- At a real point `z₋` is the complex conjugate of `z₊`. -/
theorem weightValue_conj (P : quotientFixedRing →ₐ[ℚ] ℝ) :
    complexWeightValue P (-1) = star (complexWeightValue P 1) := by
  apply Complex.ext
  · simp [complexWeightValue]
  · simp [complexWeightValue]
    ring

theorem complex_factor (P : quotientFixedRing →ₐ[ℚ] ℚ) :
    ArchimedeanQuotientLogarithm.inverseHeight (-3) 0 (baseChange ℝ P) =
      (extraFactor P : ℂ) := by
  rw [LocalHeightFormula.complex_formula, weightValue_conj, norm_star, max_self,
    CyclotomicField.finrank_eq_two, extraFactor]
  simp only [baseChange_apply, eq_ratCast, Complex.ofReal_ratCast]
  norm_num

theorem finite_one (P : quotientFixedRing →ₐ[ℚ] ℚ) (hP : AffineInvariantRing.IntegralPoint P)
    (p : Nat.Primes) :
    (QuotientFiniteFourierProduct.family p).inverseHeight (-3) 0 (finiteDiagonal P p) = 1 :=
  FiniteWeightHeight.local_height_one p _ ((IntegralPointComparison.integralPoint_iff P).mp hP p)

theorem «eqn:heightExtraFactor» : CubicTargets.ToricHeights.HeightExtraFactor.Claim where
  finite_one := finite_one
  complex P _ := complex_factor P
  height P hP := by
    have hfin : FiniteAdelicData.inverseHeight (-3) 0 (finiteDiagonal P) = 1 := by
      unfold FiniteAdelicData.inverseHeight
      calc
        _ = ∏' _ : Nat.Primes, (1 : ℂ) := tprod_congr fun p => finite_one P hP p
        _ = 1 := tprod_one
    simp only [AdelicHeightZetaData.height, AdelicData.inverseHeight, neg_zero]
    change ArchimedeanQuotientLogarithm.inverseHeight (-3) 0 (baseChange ℝ P) *
      FiniteAdelicData.inverseHeight (-3) 0 (finiteDiagonal P) = _
    rw [hfin, mul_one, complex_factor]

end Cubic.ToricHeights.HeightExtraFactor
