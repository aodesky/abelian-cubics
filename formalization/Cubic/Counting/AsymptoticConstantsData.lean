import Cubic.PoissonSummation.LeadingTermsData
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# The displayed constants in `thm:asymptoticPolynomialCount`

The original and simplified formulas are defined separately. Their equality,
convergence, and relation to the Laurent coefficients are proved in
`AsymptoticConstantIdentities`, `AsymptoticConstantsConvergence` and
`AsymptoticConstants`. In particular `classicalEulerKronecker` is only the displayed Gamma expression;
it is not a definition of the Euler–Kronecker constant of the number field.
-/

noncomputable section

namespace Cubic.Counting.AsymptoticConstantsData

open Cubic.PoissonSummation.FiniteEulerProduct

def originalInertFactor (q : InertPrimes) : ℝ := 1 - 1 / (q.1 : ℝ) ^ 2

def originalSplitFactor (p : SplitPrimes) : ℝ :=
  1 - 3 / (p.1 : ℝ) ^ 2 + 2 / (p.1 : ℝ) ^ 3

def simplifiedSplitFactor (p : SplitPrimes) : ℝ :=
  1 - 2 / ((p.1 : ℝ) * ((p.1 : ℝ) + 1))

def originalLeading : ℝ :=
  (4 * Real.pi ^ 2 / 81) * (∏' q : InertPrimes, originalInertFactor q) *
    ∏' p : SplitPrimes, originalSplitFactor p

def simplifiedLeading : ℝ := (1 / 3) * ∏' p : SplitPrimes, simplifiedSplitFactor p

def inertLogTerm (q : InertPrimes) : ℝ :=
  Real.log (q.1 : ℝ) / ((q.1 : ℝ) ^ 2 - 1)

/-- The factor `3` is outside the prime sum in the original presentation. -/
def originalSplitLogTerm (p : SplitPrimes) : ℝ :=
  ((p.1 : ℝ) - 1) * Real.log (p.1 : ℝ) / ((p.1 : ℝ) ^ 3 - 3 * (p.1 : ℝ) + 2)

def simplifiedSplitLogTerm (p : SplitPrimes) : ℝ :=
  ((2 * (p.1 : ℝ) + 1) * Real.log (p.1 : ℝ)) /
    (((p.1 : ℝ) ^ 2 - 1) * ((p.1 : ℝ) + 2))

def classicalEulerKronecker : ℝ :=
  2 * Real.eulerMascheroniConstant + Real.log (2 * Real.pi) -
    3 * Real.log (Real.Gamma (1 / 3) / Real.Gamma (2 / 3))

def originalSecondaryRatio : ℝ :=
  classicalEulerKronecker + (1 / 2) * Real.log 3 +
    (∑' q : InertPrimes, inertLogTerm q) +
    3 * (∑' p : SplitPrimes, originalSplitLogTerm p) - 1 / 2

/-- This formula takes the Euler–Kronecker constant `γ` as a parameter. -/
def simplifiedSecondaryRatio (γ : ℂ) : ℂ :=
  γ - deriv riemannZeta 2 / riemannZeta 2 + (3 / 8) * (Real.log 3 : ℂ) - 1 / 2 +
    ∑' p : SplitPrimes, (simplifiedSplitLogTerm p : ℂ)

/-- The factor from the polynomial multiplicity and the height change. -/
def leadingFromLaurent (c₂ : ℂ) : ℂ := (3 / 4) * c₂

/-- The `-c₂/2` term comes from the `1/s` in Perron's kernel. -/
def secondaryFromLaurent (c₂ c₁ : ℂ) : ℂ := (3 / 4) * (c₁ - c₂ / 2)

end Cubic.Counting.AsymptoticConstantsData
