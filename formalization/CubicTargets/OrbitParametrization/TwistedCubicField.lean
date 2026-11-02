import Cubic.OrbitParametrization.C3AlgebraTwist
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.FieldTheory.Galois.Basic
import Cubic.OrbitParametrization.TwistCohomologyData

/-!
# `example:twoRationalPointsSamePoly`

"Let `K` be a cubic abelian number field. Then `K`, equipped with its canonical Galois
action, is a `C₃`-algebra. The twist `K'` of the `C₃`-algebra `K` by the outer
automorphism `g ↦ g⁻¹` of `C₃` (with twisted action `g ∗ x = g⁻¹x`) is not isomorphic
to `K` as a `C₃`-algebra." The cohomology footnote uses the actual restriction
cocycle of the field: continuous cocycles for finite constant groups are
homomorphisms with open kernel, modulo conjugacy.

Modelling:
* A cubic abelian number field is a number field `K` with `[K:ℚ] = 3` that is Galois
  over `ℚ` (its Galois group then has order three, hence is cyclic and abelian).
* "Its canonical Galois action" requires an identification `ι : C₃ ≃* Gal(K/ℚ)`; such
  an identification exists (first conjunct), and the claim is stated for every one of
  them (there are two, differing by `g ↦ g⁻¹`).
* `C₃`-algebras are bundled (`C3Alg`), so "`K` with the action `ι` is a `C₃`-algebra"
  is stated as: some `C3Alg` is identified with `K` by a `ℚ`-algebra isomorphism `e`
  intertwining its action with `ι`. Non-isomorphism with the twist is asserted for every
  such `C3Alg`.
* The twist `C3Alg.twist` has the same algebra and action `g ∗ y = g⁻¹ y`;
  `C3Alg.Isomorphic` is existence of a `C₃`-equivariant `ℚ`-algebra isomorphism.
-/

namespace CubicTargets.OrbitParametrization.TwistedCubicField

open Cubic.OrbitParametrization.C3Algebra

def FieldClaim : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsGalois ℚ K], Module.finrank ℚ K = 3 →
    Nonempty (C3 ≃* (K ≃ₐ[ℚ] K)) ∧
    ∀ ι : C3 ≃* (K ≃ₐ[ℚ] K),
      (∃ (A : C3Alg) (e : A.carrier ≃ₐ[ℚ] K), ∀ (g : C3) (y : A.carrier), e (A.act g y) = ι g (e y)) ∧
      ∀ (A : C3Alg) (e : A.carrier ≃ₐ[ℚ] K),
        (∀ (g : C3) (y : A.carrier), e (A.act g y) = ι g (e y)) → ¬ A.Isomorphic A.twist

def Claim : Prop :=
  FieldClaim ∧ Cubic.OrbitParametrization.TwistCohomologyData.Claim

end CubicTargets.OrbitParametrization.TwistedCubicField
