import Cubic.ToricHeights.LocalWeightHeight

noncomputable section

namespace Cubic.SantensComparison.LocalHeightData

open scoped TensorProduct
open Cubic.QuadraticCorrespondence CyclotomicField CyclotomicTorusGalois
open Cubic.ToricHeights

variable {A : Type*} [CommRing A] [Algebra ℚ A] {L : Type*} [Field L]

/-- The local image of the original restriction-of-scalars parameter. -/
def nu (place : E ⊗[ℚ] A →+* L) (P : quotientFixedRing →ₐ[ℚ] A) : Lˣ :=
  Units.map place.toMonoidHom (CyclotomicRestrictionScalars.quotientRestrictionScalarsEquiv A P)

/-- Conjugation is taken in the quadratic algebra before applying the place.
At a split prime it therefore exchanges the two distinct places. -/
def nuBar (place : E ⊗[ℚ] A →+* L) (P : quotientFixedRing →ₐ[ℚ] A) : Lˣ :=
  Units.map place.toMonoidHom (CyclotomicRestrictionScalars.conjugateUnit A
    (CyclotomicRestrictionScalars.quotientRestrictionScalarsEquiv A P))

def unitAbs (q : ℕ) (ord : Lˣ →* Multiplicative ℤ) (x : Lˣ) : ℝ :=
  (q : ℝ) ^ (-(ord x).toAdd : ℝ)

def finiteFactor (place : E ⊗[ℚ] A →+* L) (P : quotientFixedRing →ₐ[ℚ] A)
    (q : ℕ) (ord : Lˣ →* Multiplicative ℤ) : ℝ :=
  (max (max 1 (unitAbs q ord (nu place P * nuBar place P)))
    (max (unitAbs q ord (nu place P ^ 2 * nuBar place P))
      (unitAbs q ord (nu place P * nuBar place P ^ 2)))) ^ (1/2 : ℝ)

def complexFactor (P : quotientFixedRing →ₐ[ℚ] ℝ) : ℝ :=
  let u := nu CyclotomicArchimedean.place.toRingHom P
  let v := nuBar CyclotomicArchimedean.place.toRingHom P
  (max (max 1 (‖((u*v : ℂˣ) : ℂ)‖ ^ 2))
    (max (‖((u^2*v : ℂˣ) : ℂ)‖ ^ 2) (‖((u*v^2 : ℂˣ) : ℂ)‖ ^ 2))) ^ (1/2 : ℝ)

end Cubic.SantensComparison.LocalHeightData
