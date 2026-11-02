import Cubic.PoissonSummation.LeadingTermsData
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# The real and arithmetic factors of the monic constants

`V(z) = ∫_{-1}^{1} (3+u²)^z du` for `z ∈ ℂ` (`eqn:monicArchimedeanFactor`) and
`𝓔_mon(z) = (1 + 2·3^{-2z}) / (3(1 + 3^{-z}) ζ(2z)) · ∏_{p ≡ 1 (3)} (1 - 2/(p^z(p^z+1)))`
(`eqn:monicEulerFactor`). The power `(3+u²)^z` is the complex power of a positive real.
-/

noncomputable section

namespace Cubic.Counting.MonicConstantsData

open Cubic.PoissonSummation.FiniteEulerProduct

/-- `V(z)`. -/
def archimedeanFactor (z : ℂ) : ℂ := ∫ u in (-1 : ℝ)..1, (((3 + u ^ 2 : ℝ)) : ℂ) ^ z

/-- The split local factor `1 - 2/(p^z(p^z+1))` of `𝓔_mon`. -/
def monicSplitFactor (p : SplitPrimes) (z : ℂ) : ℂ :=
  1 - 2 / ((p.1 : ℂ) ^ z * ((p.1 : ℂ) ^ z + 1))

/-- `𝓔_mon(z)`. -/
def monicEulerFactor (z : ℂ) : ℂ :=
  (1 + 2 * (3 : ℂ) ^ (-(2 * z))) / (3 * (1 + (3 : ℂ) ^ (-z)) * riemannZeta (2 * z)) *
    ∏' p : SplitPrimes, monicSplitFactor p z

end Cubic.Counting.MonicConstantsData
