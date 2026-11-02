import Cubic.PoissonSummation.AdelicFiniteFourierProduct

/-! # `eqn:finiteEulerBound`: domination by the convergent trivial-character product -/

noncomputable section

namespace Cubic.PoissonSummation

open MeasureTheory AdelicFourierComponents QuotientFiniteFourierProduct

/-- The finite Euler bound, retaining the real, nonnegative majorant and
convergence of its defining product. Thus the paper's `< ∞` is not inferred
from the value of a possibly nonconvergent totalized product. -/
theorem «eqn:finiteEulerBound» (s₀ σ : ℂ) (t : ℝ) (hσ : 1 < σ.re) :
    Multipliable (fun p : Nat.Primes =>
      ∫ x, finiteIntegrand p s₀.re σ.re 0 x ∂(family p).measure) ∧
    (finiteFourier s₀.re σ.re 0).im = 0 ∧
    0 ≤ (finiteFourier s₀.re σ.re 0).re ∧
    ‖finiteFourier s₀ σ t‖ ≤ (finiteFourier s₀.re σ.re 0).re := by
  have hreal := «lemma:finiteFourierProduct».trivial_value_real s₀ σ.re hσ
  exact ⟨«lemma:finiteFourierProduct».finite_convergent s₀.re σ.re 0 hσ,
    hreal.1, hreal.2, «lemma:finiteFourierProduct».domination s₀ σ t hσ⟩

end Cubic.PoissonSummation
