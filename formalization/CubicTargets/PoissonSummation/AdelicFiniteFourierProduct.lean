import Cubic.PoissonSummation.AdelicFourierComponents

/-!
# Concrete statement of `lemma:finiteFourierProduct`

The left side is the product of actual local Haar integrals of the independently
constructed adelic height and descended automorphic character. There is no
local-data parameter or assumed integral evaluation. The generic interface in
`FiniteFourierProduct` remains available for the supporting local calculations.
-/

noncomputable section

namespace CubicTargets.PoissonSummation.AdelicFiniteFourierProduct

open MeasureTheory
open Cubic.PoissonSummation.AdelicFourierComponents
open Cubic.PoissonSummation.QuotientFiniteFourierProduct
open Cubic.PoissonSummation.FiniteEulerProduct

/-- Full concrete statement of `lemma:finiteFourierProduct`.

The paper specializes to `s=(s₀,σ,σ)` and `t=m(v₀)`. All complex `s₀` and all
real `t` are retained. Local integrability and product convergence justify the
integrals and the finite trivial-character majorant. -/
structure Claim : Prop where
  local_integrable : ∀ (p : Nat.Primes) (s₀ σ : ℂ) (t : ℝ), 1 < σ.re →
    Integrable (finiteIntegrand p s₀ σ t) (family p).measure
  finite_convergent : ∀ (s₀ σ : ℂ) (t : ℝ), 1 < σ.re →
    Multipliable (fun p : Nat.Primes =>
      ∫ x, finiteIntegrand p s₀ σ t x ∂(family p).measure)
  /-- The factor `1/6` and the exact split/inert products are inside `value`. -/
  spectral_product : ∀ (s₀ σ : ℂ) (t : ℝ), 1 < σ.re →
    finiteFourier s₀ σ t = value (spectralParameter σ t)
  trivial_value_real : ∀ (s₀ : ℂ) (σ : ℝ), 1 < σ →
    (finiteFourier s₀.re σ 0).im = 0 ∧ 0 ≤ (finiteFourier s₀.re σ 0).re
  domination : ∀ (s₀ σ : ℂ) (t : ℝ), 1 < σ.re →
    ‖finiteFourier s₀ σ t‖ ≤ (finiteFourier s₀.re σ.re 0).re
  analytic : FiniteFourierProduct.AnalyticClaim

end CubicTargets.PoissonSummation.AdelicFiniteFourierProduct
