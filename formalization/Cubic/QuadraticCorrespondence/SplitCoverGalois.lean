import Cubic.QuadraticCorrespondence.SplitCoverFunctor
import Cubic.QuadraticCorrespondence.SplitLaurentGalois

/-!
# Galois compatibility with the original cover

The coefficient automorphism on the original convolution algebra exchanges
its two nontrivial characters while conjugating their values. This agrees
with the semilinear action on the Laurent presentation over every coefficient
algebra equipped with a compatible automorphism.
-/

noncomputable section

namespace Cubic.QuadraticCorrespondence.SplitCoverGalois

open Cubic.OrbitParametrization.CyclicGroupAlgebra
open Cubic.ToricHeights.TraceOneCharacters
open SplitCoverFunctor SplitLaurentInvariants SplitLaurentGalois

variable {F K R : Type*} [Field F] [Field K] [CharZero K] [Algebra F K]
variable [CommRing R] [Algebra K R] [Algebra F R]
variable (ζ : K) (hζ : ζ ^ 2 + ζ + 1 = 0)
variable (γ : K ≃ₐ[F] K) (hζγ : γ ζ = ζ ^ 2)
variable (γR : R ≃ₐ[F] R)
variable (hγR : ∀ c : K, γR (algebraMap K R c) = algebraMap K R (γ c))

include hζγ hγR

/-- Conjugation on the group-algebra coefficients gives the paper's
twisted exchange of its two characters. -/
theorem charactersOverAlgebra_conjugate (g : traceOneUnits R) :
    charactersOverAlgebra ζ hζ (mapUnits γR.toRingHom g) =
      pointConjugate γR (charactersOverAlgebra ζ hζ g) := by
  have hs : γR (algebraMap K R ζ) = (algebraMap K R ζ) ^ 2 := by
    rw [hγR, hζγ, map_pow]
  apply Prod.ext
  · apply Units.ext
    change (firstCharacter (algebraMap K R ζ) _ (mapUnits γR.toRingHom g) : R) =
      γR (secondCharacter (algebraMap K R ζ) _ g : R)
    simp only [firstCharacter, character_val, secondCharacter_val, mapUnits_coefficient,
      map_add, map_mul, map_pow, hs, ← pow_mul,
      root_fourth (algebraMap K R ζ) (root_relation ζ hζ)]
    rfl
  · apply Units.ext
    change (secondCharacter (algebraMap K R ζ) _ (mapUnits γR.toRingHom g) : R) =
      γR (firstCharacter (algebraMap K R ζ) _ g : R)
    simp only [firstCharacter, character_val, secondCharacter_val, mapUnits_coefficient,
      map_add, map_mul, map_pow, hs, ← pow_mul,
      root_fourth (algebraMap K R ζ) (root_relation ζ hζ)]
    rfl

/-- The Laurent-ring Galois action is the one induced by the original
cover, with arbitrary compatible coefficient algebras allowed. -/
theorem coverPointEquiv_conjugate (g : traceOneUnits R) (f : LaurentRing (K := K)) :
    coverPointEquiv ζ hζ (mapUnits γR.toRingHom g) (conjugate γ f) =
      γR (coverPointEquiv ζ hζ g f) := by
  rw [coverPointEquiv_apply, charactersOverAlgebra_conjugate ζ hζ γ hζγ γR hγR,
    coverPointEquiv_apply]
  exact evaluate_conjugate γ γR hγR _ f

end Cubic.QuadraticCorrespondence.SplitCoverGalois
