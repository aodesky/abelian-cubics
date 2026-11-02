import Cubic.PoissonSummation.AdelicQuotientMeasure

/-!
# Unconditional spatial and periodization convergence

Finite-stage integrals and monotone convergence give spatial integrability.
Counting-normalized unfolding with coordinate measure `du/6` supplies a
summable base point. The support-function translation bound then gives
absolute and locally uniform convergence and continuity everywhere.
This supporting result uses no Poisson hypothesis.
-/

namespace Cubic.PoissonSummation

theorem adelicPeriodizationConvergence :
    CubicTargets.PoissonSummation.AdelicPeriodizationConvergence.Claim :=
  AdelicUnfolding.convergence_of_finitePrincipalization PrimePrincipalization.finitePrincipalization

end Cubic.PoissonSummation
