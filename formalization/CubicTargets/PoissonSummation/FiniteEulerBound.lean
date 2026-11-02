import Cubic.PoissonSummation.AdelicFiniteFourierProduct

/-! # Target for `eqn:finiteEulerBound`: domination of the finite Fourier product by the
convergent, real, nonnegative trivial-character product. -/

noncomputable section

namespace CubicTargets.PoissonSummation.FiniteEulerBound

open MeasureTheory Cubic.PoissonSummation Cubic.PoissonSummation.AdelicFourierComponents
open Cubic.PoissonSummation.QuotientFiniteFourierProduct

def Claim : Prop := ∀ (s₀ σ : ℂ) (t : ℝ), 1 < σ.re →
  Multipliable (fun p : Nat.Primes =>
    ∫ x, finiteIntegrand p s₀.re σ.re 0 x ∂(family p).measure) ∧
  (finiteFourier s₀.re σ.re 0).im = 0 ∧
  0 ≤ (finiteFourier s₀.re σ.re 0).re ∧
  ‖finiteFourier s₀ σ t‖ ≤ (finiteFourier s₀.re σ.re 0).re

end CubicTargets.PoissonSummation.FiniteEulerBound
