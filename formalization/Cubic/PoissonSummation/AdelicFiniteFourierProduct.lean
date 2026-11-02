import CubicTargets.PoissonSummation.AdelicFiniteFourierProduct

/-!
# `lemma:finiteFourierProduct`

`AdelicFourierComponents` restricts the actual adelic height and descended
automorphic character to each original local point group. The proved
measure-preserving comparisons evaluate these integrals, including the
index-six cutoff at three. `QuotientFiniteFourierProduct` assembles their
convergent product and the domination and half-plane estimates.

The target retains every paper conclusion without a local-data hypothesis.
It concerns the finite part, defined in the paper as a product of local
integrals; no global Haar/Fubini or Poisson theorem is assumed.
-/

noncomputable section

namespace Cubic.PoissonSummation

open AdelicFourierComponents

/-- The finite Fourier lemma, including actual integral convergence and all
analytic clauses on `Re λ > 1`. The spectral convention is `λ = σ - π i t`. -/
theorem «lemma:finiteFourierProduct» :
    CubicTargets.PoissonSummation.AdelicFiniteFourierProduct.Claim where
  local_integrable := finite_integrable
  finite_convergent := finite_integrals_multipliable
  spectral_product := finite_integrals_product
  trivial_value_real := by
    intro s₀ σ hσ
    simp only [finiteFourier_eq]
    exact QuotientFiniteFourierProduct.finiteFourier_claim.trivial_value_real s₀ σ hσ
  domination := by
    intro s₀ σ t hσ
    simp only [finiteFourier_eq]
    exact QuotientFiniteFourierProduct.finiteFourier_claim.domination s₀ σ t hσ
  analytic := finiteEulerProduct_analytic

end Cubic.PoissonSummation
