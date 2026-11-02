import Cubic.QuadraticCorrespondence.RationalCorrespondence
import CubicTargets.QuadraticCorrespondence.IntegralityConditions

/-! # Proof of `eqn:integralityConditionsUsingCyclo` -/

namespace Cubic.QuadraticCorrespondence.IntegralityConditions

theorem «eqn:integralityConditionsUsingCyclo» :
    CubicTargets.QuadraticCorrespondence.IntegralityConditions.Claim :=
  RationalCorrespondence.integrality_iff

end Cubic.QuadraticCorrespondence.IntegralityConditions
