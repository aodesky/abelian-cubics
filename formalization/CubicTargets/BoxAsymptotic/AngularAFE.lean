import Cubic.BoxAsymptotic.AngularAFEData

namespace CubicTargets.BoxAsymptotic

open Cubic.BoxAsymptotic.AngularAFEData

/-- `lem:angularAFE`: existence of a single family of continuously differentiable
weights with uniform small-argument and cubic-decay bounds, the exact ideal AFE,
absolute convergence of both sums, and the uniform dual prefactor estimate. -/
def AngularAFEClaim : Prop :=
  ∃ (L : ℤ → ℂ → ℂ) (V : ℤ → ℂ → ℝ → ℂ) (ε : ℤ → ℂ),
    Continuation L ∧ RootNumbers L ε ∧ WeightBounds V ∧ Equations L V ε ∧ PrefactorBounds ε

end CubicTargets.BoxAsymptotic
