import Cubic.PoissonSummation.AdelicFiniteFourierProduct

/-! # Target for `eqn:finiteSpectralProduct`: the evaluated product of the actual local
integrals equals the finite Euler product `value` at the spectral parameter. -/

noncomputable section

namespace CubicTargets.PoissonSummation.FiniteSpectralProduct

open Cubic.PoissonSummation Cubic.PoissonSummation.AdelicFourierComponents
open Cubic.PoissonSummation.FiniteEulerProduct

def Claim : Prop := ∀ (s₀ σ : ℂ) (t : ℝ), 1 < σ.re →
  finiteFourier s₀ σ t = value (spectralParameter σ t)

end CubicTargets.PoissonSummation.FiniteSpectralProduct
