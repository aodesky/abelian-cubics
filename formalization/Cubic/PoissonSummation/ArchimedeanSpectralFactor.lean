import CubicTargets.PoissonSummation.ArchimedeanSpectralFactor
import Cubic.PoissonSummation.ArchimedeanTorusFourier

/-!
# `eqn:archimedeanSpectralFactor`

The original torus has a constructed, unique Haar measure with the paper's
logarithmic normalization. The actual adelic height and descended automorphic
character restrict to the coordinate integrand. Its integrability and both
displayed integral formulas transfer through the proved pushforward measure.
-/

namespace Cubic.PoissonSummation

/-- Both displayed archimedean formulas, with the actual normalized torus integral. -/
theorem «eqn:archimedeanSpectralFactor» :
    CubicTargets.PoissonSummation.ArchimedeanSpectralFactor.Claim where
  exists_measure := ⟨ArchimedeanHaar.measure, ArchimedeanHaar.normalized⟩
  unique_measure := ArchimedeanHaar.unique
  integrable := fun μ hμ s₀ σ t h₀ hσ =>
    ArchimedeanTorusFourier.integrable μ hμ s₀ σ t h₀ (lt_trans zero_lt_one hσ)
  sum_formula := fun μ hμ s₀ σ t h₀ hσ =>
    ArchimedeanTorusFourier.fourier_eq_sum μ hμ s₀ σ t h₀ (lt_trans zero_lt_one hσ)
  fraction_formula := fun μ hμ s₀ σ t h₀ hσ =>
    ArchimedeanTorusFourier.fourier_eq_fraction μ hμ s₀ σ t h₀ (lt_trans zero_lt_one hσ)

end Cubic.PoissonSummation
