import Cubic.PoissonSummation.IntegralHeightIndex
import Cubic.ToricHeights.AffineFunctionIntegrality
import CubicTargets.ToricHeights.AffineIntegralPoints

/-!
# The original all-functions integral points equal the analytic cutoff

The affine chart's integral invariant ring is defined before restricting its
functions to the torus. Every such restriction is integral over the original
cubic coefficient algebra. Integer coefficients therefore force all rational
function values to be integers; conversely the two coefficients themselves
are invariant integral polynomials. The already proved local/global rational
integrality criterion then identifies this point set with the analytic cutoff.

This proves the pointwise assertion needed by the introductory theorem.
It does not assert the stronger generation statement in `lemma:affineIntegrality`.
-/

noncomputable section

namespace Cubic.PoissonSummation.IntegralPointComparison

open Cubic.QuadraticCorrespondence.DescendedCoefficients
open Cubic.ToricHeights AdelicHeightZetaData RationalAdelicEmbedding

local instance primeFact (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

theorem coefficient_criterion : CubicTargets.ToricHeights.AffineIntegralPoints.Claim := by
  intro P
  constructor
  · exact AffineInvariantRing.coefficients_of_integralPoint P
  · rintro ⟨ha, hb⟩ f
    exact AffineFunctionIntegrality.integralPoint_of_coefficients P ha hb
      ⟨AffineInvariantRing.invariantRestriction f, AffineInvariantRing.invariantRestriction_mem f⟩

/-- The defining point-set comparison, retaining every original invariant polynomial. -/
theorem integralPoint_iff (P : RationalPoints) :
    AffineInvariantRing.IntegralPoint P ↔ diagonal P ∈ integralLocus := by
  rw [coefficient_criterion P]
  constructor
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    change ∀ p : Nat.Primes, localPoint p P ∈ (QuotientFiniteFourierProduct.family p).integralLocus
    intro p
    rw [IntegralHeightIndex.local_integral_iff, originalEquiv_localPoint]
    change ‖(P linearCoefficient : ℚ_[p])‖ ≤ 1 ∧ ‖(P constantCoefficient : ℚ_[p])‖ ≤ 1
    rw [ha, hb]
    norm_cast
    exact ⟨Padic.norm_int_le_one a, Padic.norm_int_le_one b⟩
  · intro hP
    let Q : IntegralRationalPoints := ⟨P, hP⟩
    exact ⟨⟨_, Rat.eq_num_of_isInt (IntegralHeightIndex.linear_isInt Q)⟩,
      ⟨_, Rat.eq_num_of_isInt (IntegralHeightIndex.constant_isInt Q)⟩⟩

/-- The identity on rational quotient points gives the canonical comparison of point types. -/
def integralPointsEquiv :
    {P : RationalPoints // AffineInvariantRing.IntegralPoint P} ≃ IntegralRationalPoints :=
  Equiv.subtypeEquivRight integralPoint_iff

end Cubic.PoissonSummation.IntegralPointComparison
