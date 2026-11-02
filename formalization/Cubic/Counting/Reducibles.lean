import Cubic.Counting.WeightedCount
import CubicTargets.Counting.Reducibles

/-! # `lemma:reducibles` -/

namespace Cubic.Counting.Reducibles

theorem «lemma:reducibles» : CubicTargets.Counting.Reducibles.Claim :=
  Cubic.Counting.WeightedCount.«eqn:weightedPolynomialCount»

end Cubic.Counting.Reducibles
