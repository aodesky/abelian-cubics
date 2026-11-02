import Cubic.PoissonSummation.FiniteAdelicData

/-!
# Fourier factors of the finite adelic constructions

Restrict the finite adelic height and logarithmic character to a single local
component, then form the actual Haar integral with the original invariant
cutoff. The restriction theorems identify it with the already evaluated local
Fourier integral. Pointwise finite support of the adelic height does not prove
convergence of this product of integrals: the latter uses the analytic theorem.

`AdelicFourierComponents` supplies the comparison with the full adelic height
and descended automorphic character.
-/

noncomputable section

namespace Cubic.PoissonSummation.FiniteAdelicFourier

open MeasureTheory
open QuotientFiniteFourierProduct FiniteAdelicData FiniteEulerProduct

/-- The local Fourier integrand obtained by restricting the finite adelic constructions. -/
def integrand (p : Nat.Primes) (s₀ σ : ℂ) (t : ℝ) (x : (family p).Carrier) : ℂ :=
  (family p).integralLocus.indicator (fun y => inverseHeight s₀ σ (includeLocal p y)) x *
    ((character t (includeLocal p x) : Circle) : ℂ)⁻¹

theorem integrand_eq (p : Nat.Primes) (s₀ σ : ℂ) (t : ℝ) :
    integrand p s₀ σ t =
      CubicTargets.PoissonSummation.FiniteFourierProduct.localIntegrand (family p) s₀ σ t := by
  funext x
  by_cases hx : x ∈ (family p).integralLocus <;>
    simp [integrand, CubicTargets.PoissonSummation.FiniteFourierProduct.localIntegrand,
      hx, inverseHeight_includeLocal, character_includeLocal]

/-- Haar integral of the restricted finite adelic height and character. -/
def localFourier (p : Nat.Primes) (s₀ σ : ℂ) (t : ℝ) : ℂ :=
  ∫ x, integrand p s₀ σ t x ∂(family p).measure

theorem localFourier_eq (p : Nat.Primes) (s₀ σ : ℂ) (t : ℝ) :
    localFourier p s₀ σ t =
      CubicTargets.PoissonSummation.FiniteFourierProduct.localFourier (family p) s₀ σ t := by
  rw [localFourier, integrand_eq]
  rfl

theorem local_integrable (p : Nat.Primes) (s₀ σ : ℂ) (t : ℝ) (hσ : 1 < σ.re) :
    Integrable (integrand p s₀ σ t) (family p).measure := by
  rw [integrand_eq]
  exact finiteFourier_claim.local_integrable p s₀ σ t hσ

/-- The paper's finite Fourier part, as a product of the restricted local integrals. -/
def fourierProduct (s₀ σ : ℂ) (t : ℝ) : ℂ := ∏' p : Nat.Primes, localFourier p s₀ σ t

theorem fourierProduct_eq (s₀ σ : ℂ) (t : ℝ) :
    fourierProduct s₀ σ t =
      CubicTargets.PoissonSummation.FiniteFourierProduct.finiteFourier family s₀ σ t := by
  simp only [fourierProduct, localFourier_eq,
    CubicTargets.PoissonSummation.FiniteFourierProduct.finiteFourier]

theorem multipliable_localFourier (s₀ σ : ℂ) (t : ℝ) (hσ : 1 < σ.re) :
    Multipliable (fun p => localFourier p s₀ σ t) := by
  simp only [localFourier_eq]
  exact finiteFourier_claim.finite_convergent s₀ σ t hσ

/-- Exact spectral product for these finite adelic height and character components. -/
theorem spectral_product (s₀ σ : ℂ) (t : ℝ) (hσ : 1 < σ.re) :
    fourierProduct s₀ σ t = value (spectralParameter σ t) := by
  rw [fourierProduct_eq]
  exact finiteFourier_claim.spectral_product s₀ σ t hσ

theorem domination (s₀ σ : ℂ) (t : ℝ) (hσ : 1 < σ.re) :
    ‖fourierProduct s₀ σ t‖ ≤ (fourierProduct s₀.re σ.re 0).re := by
  simp only [fourierProduct_eq]
  exact finiteFourier_claim.domination s₀ σ t hσ

theorem half_plane_bound (τ : ℝ) (hτ : 1 < τ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s₀ σ : ℂ) (t : ℝ), τ ≤ σ.re →
      ‖fourierProduct s₀ σ t‖ ≤ C := by
  simp only [fourierProduct_eq]
  exact finiteFourier_half_plane_bound τ hτ

end Cubic.PoissonSummation.FiniteAdelicFourier
