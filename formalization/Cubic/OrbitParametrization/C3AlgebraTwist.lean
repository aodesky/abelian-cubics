import Cubic.OrbitParametrization.C3Algebra

/-!
# Twisting a `C₃`-algebra by the outer automorphism of `C₃`

The warning before `thm:modularInterpretation`: the `G`-action on a `G`-algebra may be
twisted by an outer automorphism of `G`. For `G = C₃` the only nontrivial automorphism
is `g ↦ g⁻¹`, and the twist `K'` of `K` has the same underlying `ℚ`-algebra with the
action `g ∗ y = g⁻¹ y`.

The twist is again a `C₃`-algebra in the sense of `C3Alg`: in the field case the twisted
action is still faithful; in the split case the coordinate reflection `h ↦ -h`
transports the twisted action to translation.

Two `C₃`-algebras are isomorphic if there is a `C₃`-equivariant `ℚ`-algebra isomorphism
between them.
-/

noncomputable section

namespace Cubic.OrbitParametrization.C3Algebra

/-- The coordinate reflection `f ↦ (h ↦ f(-h))` of `ℚ³`. -/
def reflect : (ZMod 3 → ℚ) ≃ₐ[ℚ] (ZMod 3 → ℚ) where
  toFun f h := f (-h)
  invFun f h := f (-h)
  left_inv f := by ext h; simp
  right_inv f := by ext h; simp
  map_mul' f g := rfl
  map_add' f g := rfl
  commutes' q := rfl

/-- The twist of a `C₃`-algebra by the automorphism `g ↦ g⁻¹` of `C₃`:
same `ℚ`-algebra, action `g ∗ y = g⁻¹ y`. -/
def C3Alg.twist (K : C3Alg) : C3Alg where
  carrier := K.carrier
  act := K.act.comp (invMonoidHom (α := C3))
  model := by
    rcases K.model with ⟨hK, hdim, hinj⟩ | ⟨e, he⟩
    · exact Or.inl ⟨hK, hdim, hinj.comp inv_injective⟩
    · refine Or.inr ⟨e.trans reflect, fun g y h => ?_⟩
      change e (K.act g⁻¹ y) (-h) = e y (-(h + Multiplicative.toAdd g))
      rw [he, toAdd_inv, neg_add]

@[simp] theorem C3Alg.twist_act (K : C3Alg) (g : C3) (y : K.carrier) :
    K.twist.act g y = K.act g⁻¹ y := rfl

/-- `K` and `L` are isomorphic as `C₃`-algebras. -/
def C3Alg.Isomorphic (K L : C3Alg) : Prop :=
  ∃ e : K.carrier ≃ₐ[ℚ] L.carrier, ∀ (g : C3) (y : K.carrier), e (K.act g y) = L.act g (e y)

end Cubic.OrbitParametrization.C3Algebra
