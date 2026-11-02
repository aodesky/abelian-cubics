import Cubic.BoxAsymptotic.AngularMomentData
import Cubic.BoxAsymptotic.AngularCorrectionProduct

/-! The actual ideal Dirichlet-series identity `eq:Dk`.  The correction
product is independently defined from the displayed prime factors.
-/

namespace CubicTargets.BoxAsymptotic

open Cubic.BoxAsymptotic

def AngularEulerProductClaim : Prop :=
  ∀ k : ℤ, Even k → ∀ s : ℂ, 1 < s.re →
    AngularIdealData.idealSeries k s =
      AngularMomentData.heckeSeries k s * AngularMomentData.heckeSeries (3 * k) s *
        AngularCorrectionProduct.value k s

end CubicTargets.BoxAsymptotic
