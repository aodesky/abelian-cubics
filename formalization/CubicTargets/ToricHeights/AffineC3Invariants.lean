import Cubic.ToricHeights.AffineChartInvariants

/-!
# `eqn:affineC3invariants`

`ℤ[X/ε, Y/ε]^{C₃} = ℤ[e₂, e₃, δ]`. The left side is `AffineInvariantRing.invariants`, the
fixed ring of the cyclic generator `(x,y,z) ↦ (z,x,y)` on the chart ring
`ℤ[x,y]`, `x = X/ε`, `y = Y/ε`, `z = 1-x-y`; the right side is the `ℤ`-subalgebra generated
by the dehomogenized invariants of `AffineChartInvariants`.
-/

namespace CubicTargets.ToricHeights.AffineC3Invariants

open Cubic.ToricHeights AffineChartInvariants

def Claim : Prop :=
  AffineInvariantRing.invariants = Algebra.adjoin ℤ {e2, e3, delta}

end CubicTargets.ToricHeights.AffineC3Invariants
