import CubicTargets.PoissonSummation.InfiniteHeightFourierTransform
import Cubic.PoissonSummation.ArchimedeanHeightFourier

/-!
# `eqn:infiniteHeightFourierTransform`

The proof follows the paper, using `ArchimedeanHeightFourier.fourier_eq_formula`.

* `1_∞^{D₀} = 1`, and `H_∞(x,-s) = e^{φ(ℓ_w x)}` with `ℓ_w(x) = c(x) v₀`.
* `χ(x) = e(c(x) m(v₀))`, and `c` pushes `d^×x_∞` forward to `du`.
* The integral over `𝔱_w` splits over the two rays `u ≥ 0` and `u ≤ 0`, giving
  `(s₀ + 2πi m(v₀))^{-1} + (s₁ + s₂ - 2πi m(v₀))^{-1}`
  (`ArchimedeanFourier.integral_positive`, `integral_negative`, `fourier_eq_sum`).
* This is rewritten in the paper's `2πi` form (`ArchimedeanFourier.fourier_eq_paper_factor`).
-/

namespace Cubic.PoissonSummation.InfiniteHeightFourierTransform

theorem «eqn:infiniteHeightFourierTransform» :
    CubicTargets.PoissonSummation.InfiniteHeightFourierTransform.Claim :=
  fun χ m _ _ hexp s₀ σ h₀ hσ => ArchimedeanHeightFourier.fourier_eq_formula χ m hexp s₀ σ h₀ hσ

end Cubic.PoissonSummation.InfiniteHeightFourierTransform
