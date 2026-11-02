import Cubic.PoissonSummation.HeightCountingData
import Cubic.PoissonSummation.HeightDivisorNormalization
import Cubic.ToricHeights.AffineInvariantRing
import Cubic.PoissonSummation.LeadingTermsData
import Cubic.QuadraticCorrespondence.CyclotomicField
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.Analysis.Meromorphic.Order

/-!
# Full concrete target for `thm:heightZetaFunctionFormula`

This is the introductory theorem, distinct from the multivariate theorem
`thm:heightZetaFunctionFormula2`. The count is of fibers of the original
height, with explicit finiteness. The Euler expression uses mathlib's actual
ideal-counting Dedekind zeta in its convergence half-plane. Continuation is
given by a meromorphic witness agreeing with the original series.
The point-comparison field identifies the finite cutoff with integer values
of every element of the original integral affine invariant polynomial ring.
The normalization field identifies this original height with the height
descended to the complexified integral Cartier classes, in the coordinate
sending their computed primitive strictly convex generator to three.

No field, point space, height, coefficient sequence or analytic hypothesis is
supplied as arbitrary data. This target is a proposition, not an axiom.
-/

namespace CubicTargets.PoissonSummation.HeightZetaCountingFormula

open Cubic.PoissonSummation AdelicHeightZetaData HeightCountingData FiniteEulerProduct

structure Claim : Prop where
  integral_point_comparison : ∀ P : RationalPoints,
    Cubic.ToricHeights.AffineInvariantRing.IntegralPoint P ↔
      RationalAdelicEmbedding.diagonal P ∈ integralLocus
  height_normalization : ∀ (s : ℂ) (P : RationalPoints),
    HeightDivisorNormalization.normalizedHeight s P =
      height s 0 (RationalAdelicEmbedding.diagonal P)
  series_absolute : ∀ s : ℂ, 2 < s.re →
    Summable (fun P : IntegralRationalPoints => ‖zetaTerm s 0 P‖)
  euler_formula : ∀ s : ℂ, 2 < s.re →
    heightZeta s 0 =
      NumberField.dedekindZeta Cubic.QuadraticCorrespondence.CyclotomicField.E (s / 2) ^ 2 *
        LeadingTermsData.correction s
  inert_product_absolute : ∀ s : ℂ, 1 < s.re →
    Summable (fun q : InertPrimes => ‖HeightZetaCorrectionProduct.inert q (s / 2) - 1‖)
  split_product_absolute : ∀ s : ℂ, 1 < s.re →
    Summable (fun p : SplitPrimes => ‖HeightZetaCorrectionProduct.split p (s / 2) - 1‖)
  continuation : ∃ F : ℂ → ℂ,
    (∀ s : ℂ, 2 < s.re → F s = heightZeta s 0) ∧
    MeromorphicOn F {s : ℂ | 1 < s.re} ∧
    (∀ s : ℂ, 1 < s.re → s ≠ 2 → AnalyticAt ℂ F s) ∧
    meromorphicOrderAt F 2 = (-2 : ℤ)
  fiber_finite : ∀ n : ℕ, Finite (Fiber n)
  point_count : ∀ n : ℕ, 0 < n → ¬ 3 ∣ n → (count n : ℤ) = divisorFormula n

end CubicTargets.PoissonSummation.HeightZetaCountingFormula
