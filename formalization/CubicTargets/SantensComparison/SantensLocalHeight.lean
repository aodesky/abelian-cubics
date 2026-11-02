import Cubic.SantensComparison.LocalHeightData

namespace CubicTargets.SantensComparison.SantensLocalHeight

open Cubic.SantensComparison.LocalHeightData
open Cubic.ToricHeights Cubic.QuadraticCorrespondence CyclotomicTorusGalois
open Cubic.OrbitParametrization

/-- All local points, with both split places multiplied and the unique inert,
ramified and complex places using the global exponent one half. -/
structure Claim : Prop where
  split : ∀ (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 1)]
    (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]),
    QuotientFiniteHeight.splitInverseHeight p (-3) 0 P =
      ((finiteFactor (SplitQuotientLogarithm.place p) P
        (Nat.card (IsLocalRing.ResidueField ℤ_[p])) (PadicMultiplicative.valuation p) *
        finiteFactor (SplitQuotientLogarithm.secondPlace p) P
        (Nat.card (IsLocalRing.ResidueField ℤ_[p])) (PadicMultiplicative.valuation p) : ℝ) : ℂ)
  inert : ∀ (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 2)]
    (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]),
    QuotientFiniteHeight.inertInverseHeight p (-3) 0 P =
      (finiteFactor (InertQuotientLogarithm.place p).toRingHom P
        (Nat.card (IsLocalRing.ResidueField (CyclotomicInertField.integers p)))
        (InertLocalModel.integerValuation p) : ℂ)
  ramified : ∀ P : quotientFixedRing →ₐ[ℚ] ℚ_[3],
    QuotientFiniteHeight.ramifiedInverseHeight (-3) 0 P =
      (finiteFactor RamifiedQuotientLogarithm.place.toRingHom P
        (Nat.card (IsLocalRing.ResidueField CyclotomicRamifiedField.integers))
        RamifiedLocalModel.integerValuation : ℂ)
  complex : ∀ P : quotientFixedRing →ₐ[ℚ] ℝ,
    ArchimedeanQuotientLogarithm.inverseHeight (-3) 0 P = (complexFactor P : ℂ)

end CubicTargets.SantensComparison.SantensLocalHeight
