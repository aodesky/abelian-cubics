import Cubic.PoissonSummation.QuotientLocalFourier

/-!
# The finite Fourier product on original quotient points

Assemble the local integrals whose heights use the actual invariant-character
valuations and residue/global-degree weights. Their measures are normalized
Haar measures on the original point spaces, and their cutoffs use the original
three invariant functions. The left side remains a product of Bochner integrals.

The full analytic claim follows from the proved local comparisons.
`AdelicFourierComponents` identifies these with the adelic height and descended
automorphic-character components; `AdelicFiniteFourierProduct` proves the paper label.
-/

noncomputable section

namespace Cubic.PoissonSummation.QuotientFiniteFourierProduct

open Cubic.QuadraticCorrespondence.CyclotomicTorusGalois
open CubicTargets.PoissonSummation.FiniteFourierProduct
open FiniteEulerProduct QuotientLocalFourier

local instance primeFact (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

/-- Original local quotient-point data, selected by the rational prime's splitting type. -/
def family (p : Nat.Primes) : LocalData :=
  if h : (p : ℕ) % 3 = 1 then splitData ⟨p, h⟩
  else if h : (p : ℕ) % 3 = 2 then inertData ⟨p, h⟩
  else ramifiedData

@[simp]
theorem family_split (p : SplitPrimes) : family p.1 = splitData p := by
  simp [family, p.property]

@[simp]
theorem family_inert (p : InertPrimes) : family p.1 = inertData p := by
  simp [family, p.property]

@[simp]
theorem family_three : family primeThree = ramifiedData := by
  simp [family, primeThree]

/-- Every branch uses points of the original quotient over the indexed local field.
In particular the exceptional branch occurs only at three. -/
theorem family_carrier (p : Nat.Primes) :
    (family p).Carrier = (quotientFixedRing →ₐ[ℚ] ℚ_[p]) := by
  by_cases h1 : (p : ℕ) % 3 = 1
  · simp [family, h1, splitData]
  by_cases h2 : (p : ℕ) % 3 = 2
  · simp [family, h2, inertData]
  have h0 : (p : ℕ) % 3 = 0 := by omega
  have hp : p = primeThree := Subtype.ext
    ((p.property.dvd_iff_eq (by decide)).mp (Nat.dvd_of_mod_eq_zero h0))
  subst p
  rfl

/-- All local integrability and Fourier evaluations on the original quotient are proved. -/
theorem localCalculation : LocalCalculation family where
  integrable := by
    intro p s₀ σ t hσ
    by_cases h1 : (p : ℕ) % 3 = 1
    · rw [family_split ⟨p, h1⟩]
      exact (integral_eq_splitFactor ⟨p, h1⟩ s₀ σ t hσ).1
    by_cases h2 : (p : ℕ) % 3 = 2
    · rw [family_inert ⟨p, h2⟩]
      exact (integral_eq_inertFactor ⟨p, h2⟩ s₀ σ t hσ).1
    · have hf : family p = ramifiedData := by simp [family, h1, h2]
      rw [hf]
      exact (integral_eq_one_sixth s₀ σ t).1
  split := by
    intro p s₀ σ t hσ
    rw [family_split]
    exact (integral_eq_splitFactor p s₀ σ t hσ).2
  inert := by
    intro p s₀ σ t hσ
    rw [family_inert]
    exact (integral_eq_inertFactor p s₀ σ t hσ).2
  at_three := by
    intro s₀ σ t _
    rw [family_three]
    exact (integral_eq_one_sixth s₀ σ t).2

/-- All clauses of the finite Fourier claim for these original quotient-point local data.
The subsequent adelic comparison is proved in `AdelicFourierComponents`. -/
theorem finiteFourier_claim : Claim family :=
  finiteFourierProduct_of_localCalculation localCalculation

/-- Uniform boundedness of the original quotient-point integrals, including uniformity in `t`. -/
theorem finiteFourier_half_plane_bound (τ : ℝ) (hτ : 1 < τ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s₀ σ : ℂ) (t : ℝ), τ ≤ σ.re →
      ‖finiteFourier family s₀ σ t‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := finiteFourier_claim.analytic.half_plane_bound τ hτ
  refine ⟨C, hC, ?_⟩
  intro s₀ σ t hσ
  rw [finiteFourier_claim.spectral_product s₀ σ t (hτ.trans_le hσ)]
  exact hbound (spectralParameter σ t) (by simpa using hσ)

end Cubic.PoissonSummation.QuotientFiniteFourierProduct
