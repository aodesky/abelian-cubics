import Cubic.ToricHeights.AffineInvariantRing
import Cubic.ToricHeights.AffineChartInvariants
import Cubic.PoissonSummation.AdelicHeightZetaData
import Cubic.Counting.AsymptoticConstantsData

/-! The integral point count uses the original invariant-integrality condition and height.
The product and sum below are the paper's `α` and `β`; no counting assertion is used
in their definitions. -/

noncomputable section

namespace Cubic.Counting.IntegralPointCountData

open Cubic.PoissonSummation Cubic.PoissonSummation.AdelicHeightZetaData
open Cubic.Counting.AsymptoticConstantsData Cubic.PoissonSummation.FiniteEulerProduct

def boundedPoints (H : ℝ) : Set RationalPoints :=
  {P | Cubic.ToricHeights.AffineInvariantRing.IntegralPoint P ∧
    (height 1 0 (RationalAdelicEmbedding.diagonal P)).re ≤ H}

def count (H : ℝ) : ℕ := Nat.card (boundedPoints H)

/-- The full affine integral locus with the original toric height. The height is
evaluated through restriction to the torus; the proof establishes existence and
uniqueness of this extension for every affine integral point. -/
def boundedAffinePoints (H : ℝ) : Set Cubic.ToricHeights.AffineChartInvariants.RationalPoint :=
  {P | Cubic.ToricHeights.AffineChartInvariants.IsD0Integral P ∧
    ∃ Q : RationalPoints,
      Q.toRingHom.comp Cubic.ToricHeights.AffineInvariantRing.invariantRestriction.toRingHom = P ∧
        (height 1 0 (RationalAdelicEmbedding.diagonal Q)).re ≤ H}

def affineCount (H : ℝ) : ℕ := Nat.card (boundedAffinePoints H)

def alpha : ℝ := ∏' p : SplitPrimes, simplifiedSplitFactor p

def beta : ℝ := ∑' p : SplitPrimes, simplifiedSplitLogTerm p

/-- `μ` is supplied by the genuine Dedekind Euler–Kronecker characterization. -/
def Q (μ : ℂ) (X : ℝ) : ℝ :=
  (2 * alpha / 9) * (X + μ.re - (deriv riemannZeta 2 / riemannZeta 2).re +
    beta + 3 / 8 * Real.log 3 - 1 / 2)

end Cubic.Counting.IntegralPointCountData
