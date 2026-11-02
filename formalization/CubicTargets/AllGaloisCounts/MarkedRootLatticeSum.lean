import Cubic.AllGaloisCounts.MarkedLatticeData

namespace CubicTargets.AllGaloisCounts.MarkedRootLatticeSum
open Cubic.AllGaloisCounts.CountData Cubic.AllGaloisCounts.MarkedLatticeData

/-- `eqn:markedRootLatticeSum`, retaining the actual marked-root count. -/
def Claim : Prop :=
  Asymptotics.IsBigO Filter.atTop
    (fun H : ℝ => (markedCount H : ℝ) - latticeSum H) (fun H : ℝ => H ^ 2)

end CubicTargets.AllGaloisCounts.MarkedRootLatticeSum
