import Cubic.PoissonSummation.AdelicFiniteFourierProduct

/-! # `eqn:finiteSpectralProduct`: the evaluated product of actual local integrals -/

noncomputable section

namespace Cubic.PoissonSummation

open AdelicFourierComponents FiniteEulerProduct

/-- The exact finite spectral product, with the exceptional coefficient `1/6`
inside `value` and the inverse-character convention inside `finiteFourier`. -/
theorem «eqn:finiteSpectralProduct» (s₀ σ : ℂ) (t : ℝ) (hσ : 1 < σ.re) :
    finiteFourier s₀ σ t = value (spectralParameter σ t) :=
  «lemma:finiteFourierProduct».spectral_product s₀ σ t hσ

end Cubic.PoissonSummation
