import CubicTargets.Counting.TopacogullariDyadic
import Cubic.Counting.TopacogullariMeanValue

namespace Cubic.Counting.TopacogullariDyadic

theorem «eqn:topacogullari»
    (hTop : CubicTargets.Counting.TopacogullariSecondMoment.BlackBox) :
    CubicTargets.Counting.TopacogullariDyadic.Claim :=
  TopacogullariMeanValue.meanValue hTop

end Cubic.Counting.TopacogullariDyadic
