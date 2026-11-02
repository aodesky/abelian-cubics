import Cubic.PoissonSummation.SplitLocalFourier
import Cubic.PoissonSummation.InertLocalFourier
import Cubic.PoissonSummation.RamifiedLocalFourier

/-!
# The finite Fourier product for the constructed local models

Assemble the split, inert and ramified local data over all rational primes.
Every local integral is defined from its Haar measure, height, integral locus
and character. The valuation/support description is now proved for this family,
so its full Fourier-product claim has no remaining local-calculation hypotheses.

This is still a theorem about the constructed quadratic local models. The
comparison with the paper's original torus, geometric integral model, canonical
height and spectral character is not supplied by this assembly theorem.
-/

noncomputable section

namespace Cubic.PoissonSummation.LocalModelProduct

open CubicTargets.PoissonSummation.FiniteFourierProduct
open FiniteEulerProduct

/-- The actual local models, selected by the rational prime's residue class. -/
def family (p : Nat.Primes) : LocalData :=
  if h : (p : ℕ) % 3 = 1 then SplitLocalFourier.data ⟨p, h⟩
  else if h : (p : ℕ) % 3 = 2 then InertLocalFourier.data ⟨p, h⟩
  else RamifiedLocalFourier.data

@[simp]
theorem family_split (p : SplitPrimes) : family p.1 = SplitLocalFourier.data p := by
  simp [family, p.property]

@[simp]
theorem family_inert (p : InertPrimes) : family p.1 = InertLocalFourier.data p := by
  simp [family, p.property]

@[simp]
theorem family_three : family primeThree = RamifiedLocalFourier.data := by
  simp [family, primeThree]

/-- The last branch of the definition occurs only at the exceptional prime. -/
theorem prime_cases (p : Nat.Primes) :
    p = primeThree ∨ (p : ℕ) % 3 = 1 ∨ (p : ℕ) % 3 = 2 := by
  by_cases h : (p : ℕ) % 3 = 0
  · left
    exact Subtype.ext ((p.property.dvd_iff_eq (by decide)).mp (Nat.dvd_of_mod_eq_zero h))
  · right
    omega

/-- All geometric prerequisites of the assembly interface are proved for this
family. No local integrability or integral-evaluation hypotheses remain. -/
theorem valuationDescription : LocalValuationDescription family where
  split := by
    intro p
    rw [family_split]
    exact ⟨SplitLocalFourier.valuationData p,
      fun s₀ σ t _ => SplitLocalFourier.integrand_eq_lattice p s₀ σ t⟩
  inert := by
    intro p
    rw [family_inert]
    exact ⟨InertLocalFourier.valuationData p,
      fun s₀ σ t _ => InertLocalFourier.integrand_eq_lattice p s₀ σ t⟩
  at_three := by
    rw [family_three]
    refine ⟨Cubic.ToricHeights.RamifiedLocalModel.congruenceSubgroup,
      Cubic.ToricHeights.RamifiedLocalModel.measurableSet_congruenceSubgroup,
      Cubic.ToricHeights.RamifiedLocalModel.congruenceSubgroup_index, ?_⟩
    intro s₀ σ t _
    exact RamifiedLocalFourier.integrand_eq_indicator s₀ σ t

/-- The complete finite Fourier product and analytic conclusions for the local
models. This does not assert the outstanding comparison with the paper's torus. -/
theorem finiteFourier_claim : Claim family :=
  finiteFourierProduct_of_valuationDescription valuationDescription

/-- A uniform bound on the product of actual model integrals, independent of
the spectral parameter `t` and the retained divisor parameter `s₀`. -/
theorem finiteFourier_half_plane_bound (τ : ℝ) (hτ : 1 < τ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s₀ σ : ℂ) (t : ℝ), τ ≤ σ.re →
      ‖finiteFourier family s₀ σ t‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := finiteFourier_claim.analytic.half_plane_bound τ hτ
  refine ⟨C, hC, ?_⟩
  intro s₀ σ t hσ
  rw [finiteFourier_claim.spectral_product s₀ σ t (hτ.trans_le hσ)]
  exact hbound (spectralParameter σ t) (by simpa using hσ)

end Cubic.PoissonSummation.LocalModelProduct
