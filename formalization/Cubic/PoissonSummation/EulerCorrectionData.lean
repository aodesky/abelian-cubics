import Cubic.PoissonSummation.LeadingTermsData

/-! The correction factor in the current paper's variable `z`. -/

noncomputable section

namespace Cubic.PoissonSummation.EulerCorrectionData

open FiniteEulerProduct

/-- The manuscript's unramified correction product. -/
def R (z : ℂ) : ℂ :=
  (∏' q : InertPrimes, (1 - (q.1 : ℂ) ^ (-(2 * z)))) *
    (∏' p : SplitPrimes,
      (1 - 3 * (p.1 : ℂ) ^ (-(2 * z)) + 2 * (p.1 : ℂ) ^ (-(3 * z))))

/-- The Dirichlet-series variable counts squared heights. -/
def Z0 (z : ℂ) : ℂ := LeadingTermsData.heightZeta (2 * z)

/-- The total correction, retained for the internal expansion in the height variable. -/
def E (z : ℂ) : ℂ :=
  (1 - (3 : ℂ) ^ (-z)) ^ 2 *
    (∏' q : InertPrimes, (1 - (q.1 : ℂ) ^ (-(2 * z)))) *
    (∏' p : SplitPrimes,
      (1 - 3 * (p.1 : ℂ) ^ (-(2 * z)) + 2 * (p.1 : ℂ) ^ (-(3 * z))))

end Cubic.PoissonSummation.EulerCorrectionData
