import CubicTargets.Counting.XiMeanBound
import Cubic.Counting.CriticalMeanSquare
import Cubic.Analysis.UniformGaussianMeanValue
import Cubic.Analysis.ZetaStripGrowth

namespace Cubic.Counting.XiMeanBound

/-- The Gaussian contour argument, with uniformity up to the critical line. -/
theorem «eqn:xiMeanBound»
    (hCN : CubicTargets.Counting.ChandrasekharanNarasimhanMeanSquare.BlackBox) :
    CubicTargets.Counting.XiMeanBound.Claim :=
  Cubic.Analysis.UniformGaussianMeanValue.mean_value_strip
    (CriticalMeanSquare.«eqn:criticalMeanSquare» hCN) Cubic.Analysis.ZetaStripGrowth.zetaE_growth

end Cubic.Counting.XiMeanBound
