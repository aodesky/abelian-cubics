import Cubic.PoissonSummation.PoissonIntegral
import CubicTargets.PoissonSummation.PoissonEulerIntegral

/-! # Proof of `eqn:poissonEulerIntegral`: the equality of `lemma:poissonIntegral`. -/

namespace Cubic.PoissonSummation.PoissonEulerIntegral

theorem «eqn:poissonEulerIntegral»
    (hPoisson : CubicTargets.PoissonSummation.PoissonWithDualMeasure.BlackBox) :
    CubicTargets.PoissonSummation.PoissonEulerIntegral.Claim := fun s₀ σ h₀ hσ =>
  ⟨(Cubic.PoissonSummation.«lemma:poissonIntegral» hPoisson).spectral_integrable s₀ σ h₀ hσ,
    (Cubic.PoissonSummation.«lemma:poissonIntegral» hPoisson).poisson_equality s₀ σ h₀ hσ⟩

end Cubic.PoissonSummation.PoissonEulerIntegral
