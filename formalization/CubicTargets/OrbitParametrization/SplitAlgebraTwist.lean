import Cubic.OrbitParametrization.C3AlgebraTwist
import Cubic.OrbitParametrization.SplitAlgebra
import Mathlib.GroupTheory.Perm.Support

/-!
# `example:splitAlgebra`

"Let `K_spl = ℚ³`, the split cubic algebra. Then `C₃ ⊂ S₃ = Aut_{ℚ-alg}(K_spl)` and
`K_spl`, equipped with its canonical `C₃`-action, is a `C₃`-algebra. Any transposition
gives an isomorphism of `C₃`-algebras from `K_spl` to its twist `K_spl'`."

Modelling:
* `K_spl` is `ZMod 3 → ℚ` and its canonical `C₃`-action is translation,
  `(g f)(h) = f(h + g)`; this is the project's `splitAlg`, whose `model` field records
  that it is a `C₃`-algebra (the defining condition of `C3Alg`, split case).
* `S₃ = Aut(K_spl)`: permutations `π` of the coordinates `ZMod 3` act by
  `f ↦ f ∘ π⁻¹`, and this is a group isomorphism `Perm (ZMod 3) ≃* Aut_{ℚ-alg}(ℚ³)`.
  Under it `g ∈ C₃` is the translation `h ↦ h - g` of coordinates, i.e. the canonical
  action is the restriction to `C₃ ⊂ S₃`.
* The algebra automorphism given by a transposition `π` (`π.IsSwap`) is `f ↦ f ∘ π`
  (`= f ∘ π⁻¹` as `π = π⁻¹`); the claim is that it is `C₃`-equivariant from `splitAlg`
  to `splitAlg.twist`.
-/

namespace CubicTargets.OrbitParametrization.SplitAlgebraTwist

open Cubic.OrbitParametrization.C3Algebra

def Claim : Prop :=
  (∃ Φ : Equiv.Perm (ZMod 3) ≃* ((ZMod 3 → ℚ) ≃ₐ[ℚ] (ZMod 3 → ℚ)),
      (∀ (π : Equiv.Perm (ZMod 3)) (f : ZMod 3 → ℚ) (h : ZMod 3), Φ π f h = f (π⁻¹ h)) ∧
      ∀ g : C3, splitAlg.act g = Φ (Equiv.addRight (-Multiplicative.toAdd g))) ∧
  ∀ π : Equiv.Perm (ZMod 3), π.IsSwap →
    ∃ e : splitAlg.carrier ≃ₐ[ℚ] splitAlg.twist.carrier,
      (∀ (f : ZMod 3 → ℚ) (h : ZMod 3), (e f : ZMod 3 → ℚ) h = f (π h)) ∧
      ∀ (g : C3) (y : splitAlg.carrier), e (splitAlg.act g y) = splitAlg.twist.act g (e y)

end CubicTargets.OrbitParametrization.SplitAlgebraTwist
