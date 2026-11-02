import Cubic.Counting.PolynomialCountData
import Cubic.Counting.AsymptoticConstantsData
import Cubic.QuadraticCorrespondence.CyclotomicField
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.Analysis.Analytic.Basic

/-!
# Statement of `thm:asymptoticPolynomialCount`

All counts are of integer polynomials `t³-t²+at+b`. Both presentations of both
constants, their convergence, and the error exponent are included. The
Euler–Kronecker constant is characterized through the continuation of the
ideal-counting Dedekind zeta function of `ℚ(√-3)`, not defined by its Gamma-value
expression; that evaluation is part of the claim (`gamma_evaluation`).

The proof is `Cubic.Counting.AsymptoticPolynomialCount.«thm:asymptoticPolynomialCount»`,
which takes the Poisson summation input `PoissonWithDualMeasure.BlackBox` and
[Chandrasekharan–Narasimhan, Math. Ann. 152 (1963), Theorem 4]
(`ChandrasekharanNarasimhanMeanSquare.BlackBox`)
as explicit hypotheses.
-/

namespace CubicTargets.Counting.AsymptoticPolynomialCount

open Filter Asymptotics Cubic.Counting.PolynomialCountData
open Cubic.Counting.AsymptoticConstantsData Cubic.PoissonSummation.FiniteEulerProduct
open scoped Topology

/-- A continuation of the Dedekind zeta series of `ℚ(√-3)` and its Euler–Kronecker constant. -/
structure EulerKronecker (Z : ℂ → ℂ) (γ : ℂ) : Prop where
  agrees : ∀ s : ℂ, 1 < s.re →
    Z s = NumberField.dedekindZeta Cubic.QuadraticCorrespondence.CyclotomicField.E s
  analytic : ∀ s : ℂ, (1 / 2 : ℝ) < s.re → s ≠ 1 → AnalyticAt ℂ Z s
  defining_limit : Tendsto (fun s : ℂ => deriv Z s / Z s + 1 / (s - 1))
    (𝓝[≠] (1 : ℂ)) (𝓝 γ)

structure Constants (γ : ℂ) (C D : ℝ) : Prop where
  positive : 0 < C
  original_leading : C = originalLeading
  simplified_leading : C = simplifiedLeading
  original_secondary : D / C = originalSecondaryRatio
  simplified_secondary : (D / C : ℂ) = simplifiedSecondaryRatio γ
  gamma_evaluation : γ = (classicalEulerKronecker : ℂ)
  inert_product_absolute : Summable (fun q : InertPrimes => ‖originalInertFactor q - 1‖)
  split_product_absolute : Summable (fun p : SplitPrimes => ‖originalSplitFactor p - 1‖)
  simplified_product_absolute :
    Summable (fun p : SplitPrimes => ‖simplifiedSplitFactor p - 1‖)
  inert_sum_absolute : Summable (fun q : InertPrimes => ‖inertLogTerm q‖)
  split_sum_absolute : Summable (fun p : SplitPrimes => ‖originalSplitLogTerm p‖)
  simplified_sum_absolute : Summable (fun p : SplitPrimes => ‖simplifiedSplitLogTerm p‖)

/-- Finiteness of the counts and the two-term asymptotic for every positive ε. -/
structure Asymptotic (C D : ℝ) : Prop where
  finite_counts : ∀ H : ℝ, (boundedPolynomials H).Finite
  estimate : ∀ ε : ℝ, 0 < ε →
    (fun H : ℝ => (polynomialCount H : ℝ) -
      (C * H ^ 2 * Real.log H +
        (C * Real.log (Real.sqrt 3) + D - Real.pi / (3 * Real.sqrt 3)) * H ^ 2))
      =O[atTop] (fun H : ℝ => H ^ (1 + ε))

/-- `thm:asymptoticPolynomialCount`, with no data parameters or hypotheses. -/
def Claim : Prop := ∃ (Z : ℂ → ℂ) (γ : ℂ) (C D : ℝ),
  EulerKronecker Z γ ∧ Constants γ C D ∧ Asymptotic C D

end CubicTargets.Counting.AsymptoticPolynomialCount
