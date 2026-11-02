import Cubic.ToricHeights.SplitLocalHeight
import Cubic.ToricHeights.LocalCoefficientIntegrality
import Cubic.QuadraticCorrespondence.CyclotomicLocalTopology

/-!
# The coefficient-integrality cutoff at split primes

For split coordinates `x,y`, set `N=xy` and `T=x+y`. Away from three,
integrality of the two cubic coefficients is equivalent to integrality of
`x²y` and `xy²`. Their valuations give exactly the enlarged-lattice cone used
in the local Fourier calculation. For points of the original quotient,
`QuotientLocalIntegrality` identifies these coefficient expressions with the
descended cubic coefficients.
-/

noncomputable section

namespace Cubic.ToricHeights.SplitLocalIntegrality

open Cubic.QuadraticCorrespondence.CocharacterIsomorphism
open Cubic.QuadraticCorrespondence
open Cubic.PoissonSummation

variable (p : ℕ) [Fact p.Prime]

/-- The two monomials are roots of the integral quadratic from the paper's
local-integrality argument. No integrality of `x` or `y` is assumed. -/
theorem coefficientsIntegral_iff_monomials (hp : p ≠ 3) (x y : ℚ_[p]) :
    LocalCoefficientIntegrality.CoefficientsIntegral p (x * y) (x + y) ↔
      ‖x ^ 2 * y‖ ≤ 1 ∧ ‖x * y ^ 2‖ ≤ 1 := by
  rw [LocalCoefficientIntegrality.coefficientsIntegral_iff p hp]
  constructor
  · rintro ⟨hN, hNT⟩
    have hcube : ‖(x * y) ^ 3‖ ≤ 1 := by
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) hN
    exact ⟨LocalCoefficientIntegrality.norm_le_one_of_quadratic p hNT hcube (by ring),
      LocalCoefficientIntegrality.norm_le_one_of_quadratic p hNT hcube (by ring)⟩
  · rintro ⟨hs, ht⟩
    have hcube : ‖x * y‖ ^ 3 ≤ 1 := by
      rw [← norm_pow, show (x * y) ^ 3 = (x ^ 2 * y) * (x * y ^ 2) by ring, norm_mul]
      exact mul_le_one₀ hs (norm_nonneg _) ht
    refine ⟨(pow_le_one_iff_of_nonneg (norm_nonneg _) (by decide : (3 : ℕ) ≠ 0)).mp hcube, ?_⟩
    rw [show x * y * (x + y) = x ^ 2 * y + x * y ^ 2 by ring]
    exact (Padic.nonarchimedean _ _).trans (max_le hs ht)

/-- The monomial valuations are `2ν(x)+ν(y)` and `ν(x)+2ν(y)`, three times
the two ray coordinates. This uses the full enlarged cocharacter lattice. -/
theorem monomials_integral_iff_cone (x : SplitLocalModel.Points p) :
    (‖(x.1 : ℚ_[p]) ^ 2 * (x.2 : ℚ_[p])‖ ≤ 1 ∧
      ‖(x.1 : ℚ_[p]) * (x.2 : ℚ_[p]) ^ 2‖ ≤ 1) ↔
      x ∈ SplitLocalModel.integralLocus p := by
  rw [Padic.norm_le_one_iff_val_nonneg, Padic.norm_le_one_iff_val_nonneg,
    Padic.valuation_mul (pow_ne_zero 2 x.1.ne_zero) x.2.ne_zero,
    Padic.valuation_mul x.1.ne_zero (pow_ne_zero 2 x.2.ne_zero), Padic.valuation_pow,
    Padic.valuation_pow]
  change (0 ≤ 2 * Padic.valuation (x.1 : ℚ_[p]) + Padic.valuation (x.2 : ℚ_[p]) ∧
    0 ≤ Padic.valuation (x.1 : ℚ_[p]) + 2 * Padic.valuation (x.2 : ℚ_[p])) ↔
      LatticeCone.InCone (fromCyclotomic
        (Padic.valuation (x.1 : ℚ_[p]), Padic.valuation (x.2 : ℚ_[p])))
  rw [LatticeCone.inCone_iff]
  dsimp [fromCyclotomic]
  omega

/-- The cutoff defined by the paper's explicit cubic coefficients in split coordinates. -/
def coefficientLocus : Set (SplitLocalModel.Points p) :=
  {x | LocalCoefficientIntegrality.CoefficientsIntegral p
    ((x.1 : ℚ_[p]) * (x.2 : ℚ_[p])) ((x.1 : ℚ_[p]) + (x.2 : ℚ_[p]))}

theorem coefficientLocus_eq_integralLocus (hp : p ≠ 3) :
    coefficientLocus p = SplitLocalModel.integralLocus p := by
  ext x
  exact (coefficientsIntegral_iff_monomials p hp _ _).trans (monomials_integral_iff_cone p x)

/-- Under the cyclotomic splitting, the cutoff uses the same two
coefficient expressions as the inert and ramified constructions. -/
theorem splittingUnitsEquiv_mem_coefficientLocus
    (ζ : ℚ_[p]) (hζ : ζ ^ 2 + ζ + 1 = 0)
    (z : (CyclotomicLocalAlgebra.Model ℚ_[p])ˣ) (u v : ℚ_[p])
    (hz : (z : CyclotomicLocalAlgebra.Model ℚ_[p]) =
      algebraMap ℚ_[p] (CyclotomicLocalAlgebra.Model ℚ_[p]) u +
        algebraMap ℚ_[p] (CyclotomicLocalAlgebra.Model ℚ_[p]) v *
          AdjoinRoot.root (Polynomial.cyclotomic 3 ℚ_[p])) :
    CyclotomicLocalAlgebra.splittingUnitsEquiv ζ hζ z ∈ coefficientLocus p ↔
      ‖CyclotomicCoefficients.linearCoefficient u v‖ ≤ 1 ∧
        ‖CyclotomicCoefficients.constantCoefficient u v‖ ≤ 1 := by
  have hcoords :
      (((CyclotomicLocalAlgebra.splittingUnitsEquiv ζ hζ z).1 : ℚ_[p]),
        ((CyclotomicLocalAlgebra.splittingUnitsEquiv ζ hζ z).2 : ℚ_[p])) =
          (u + v * ζ, u + v * (-1 - ζ)) := by
    change CyclotomicLocalAlgebra.splittingEquiv ζ hζ (z : CyclotomicLocalAlgebra.Model ℚ_[p]) = _
    rw [hz]
    simp only [map_add, map_mul, AlgEquiv.commutes, CyclotomicLocalAlgebra.splittingEquiv_root]
    rfl
  change LocalCoefficientIntegrality.CoefficientsIntegral p _ _ ↔ _
  rw [show ((CyclotomicLocalAlgebra.splittingUnitsEquiv ζ hζ z).1 : ℚ_[p]) =
      u + v * ζ from congrArg Prod.fst hcoords,
    show ((CyclotomicLocalAlgebra.splittingUnitsEquiv ζ hζ z).2 : ℚ_[p]) =
      u + v * (-1 - ζ) from congrArg Prod.snd hcoords,
    CyclotomicCoefficients.linear_mul_conjugate ζ u v hζ,
    CyclotomicCoefficients.linear_add_conjugate]
  rfl

end Cubic.ToricHeights.SplitLocalIntegrality
