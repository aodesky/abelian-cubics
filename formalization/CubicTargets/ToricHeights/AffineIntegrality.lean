import CubicTargets.ToricHeights.AffineC3Invariants

/-!
# `lemma:affineIntegrality`

With the dehomogenized invariants `e₂, e₃, δ` on the trace-one chart
(`AffineChartInvariants`):
1. `ℤ[X/ε,Y/ε]^{C₃} = ℤ[e₂,e₃,δ]` (`eqn:affineC3invariants`);
2. a rational point `P` of `S ∖ D₀` (a ring map `ℤ[X/ε,Y/ε]^{C₃} → ℚ`, see
   `AffineChartInvariants.RationalPoint`) is `D₀`-integral (every invariant is `ℤ`-valued,
   `AffineChartInvariants.IsD0Integral`) iff `e₂(P), e₃(P) ∈ ℤ`.
-/

namespace CubicTargets.ToricHeights.AffineIntegrality

open Cubic.ToricHeights AffineChartInvariants

def Claim : Prop :=
  CubicTargets.ToricHeights.AffineC3Invariants.Claim ∧
    ∀ P : RationalPoint, IsD0Integral P ↔
      (∃ a : ℤ, P ⟨e2, e2_mem⟩ = (a : ℚ)) ∧ (∃ b : ℤ, P ⟨e3, e3_mem⟩ = (b : ℚ))

end CubicTargets.ToricHeights.AffineIntegrality
