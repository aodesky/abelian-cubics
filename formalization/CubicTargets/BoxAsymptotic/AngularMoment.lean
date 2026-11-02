import Cubic.BoxAsymptotic.AngularMomentData

/-! A concrete target for both assertions of `lem:moment`.  Existence of the
analytic realizations is part of the claim, so the target cannot be satisfied
by quantifying over an empty class of possible continuations. -/

namespace CubicTargets.BoxAsymptotic

open Cubic.BoxAsymptotic.AngularMomentData

/-- `lem:moment`, for the actual Hecke and angular Fourier coefficients. -/
def AngularMomentClaim : Prop :=
  ∃ L F : ℤ → ℂ → ℂ, AnalyticRealization L F ∧ MomentBounds L F

end CubicTargets.BoxAsymptotic
