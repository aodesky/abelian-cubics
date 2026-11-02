import Cubic.PoissonSummation.AdelicHeightZetaData
import Cubic.PoissonSummation.HeightZetaCorrectionProduct
import Cubic.PoissonSummation.QuadraticDirichletCharacter

/-!
# Objects in `prop:leadingTerms`

The one-variable height zeta function is the original series on the divisor
line `s D₀`. The correction is `(1-3^{-z})² R(z)` evaluated at `z = s/2`.
In particular, derivatives of `correction` are derivatives in `s`.
Neither a continued Dedekind zeta function nor its Euler–Kronecker constant
is defined by a conjectured formula here.
-/

noncomputable section

namespace Cubic.PoissonSummation.LeadingTermsData

open FiniteEulerProduct

def heightZeta (s : ℂ) : ℂ := AdelicHeightZetaData.heightZeta s 0

def correction (s : ℂ) : ℂ :=
  (1 - (3 : ℂ) ^ (-(s / 2))) ^ 2 * HeightZetaCorrectionProduct.value (s / 2)

/-- The simplified split local factor, in the height-series variable `s=2z`. -/
def splitFactor (p : SplitPrimes) (s : ℂ) : ℂ :=
  1 - 2 / ((p.1 : ℂ) ^ (s / 2) * ((p.1 : ℂ) ^ (s / 2) + 1))

def splitProductAtTwo : ℂ :=
  ∏' p : SplitPrimes, (1 - 2 / ((p.1 : ℂ) * ((p.1 : ℂ) + 1)))

def splitLogTerm (p : SplitPrimes) : ℂ :=
  ((2 * (p.1 : ℂ) + 1) * (Real.log (p.1 : ℝ) : ℂ)) /
    (((p.1 : ℂ) ^ 2 - 1) * ((p.1 : ℂ) + 2))

end Cubic.PoissonSummation.LeadingTermsData
