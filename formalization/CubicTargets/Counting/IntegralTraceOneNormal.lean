import Cubic.OrbitParametrization.TraceOne

/-! # Target for `lemma:integralTraceOneImpliesNormal`: an integer triple with
`α + β + γ = 1` is normal in the split `ℚ`-algebra `ℚ³`, i.e. its three cyclic
permutations are linearly independent over `ℚ` (`IsNormal`). -/

namespace CubicTargets.Counting.IntegralTraceOneNormal

open Cubic.OrbitParametrization

def Claim : Prop := ∀ α β γ : ℤ, α + β + γ = 1 → IsNormal (α : ℚ) β γ

end CubicTargets.Counting.IntegralTraceOneNormal
