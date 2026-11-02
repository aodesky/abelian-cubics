import CubicTargets.OrbitParametrization.SplitAlgebraTwist
import Cubic.OrbitParametrization.SplitAutomorphisms

/-!
# `example:splitAlgebra`

The paper gives no proof. `S₃ = Aut(ℚ³)`: a permutation `π` acts by `f ↦ f ∘ π⁻¹`;
every `ℚ`-algebra automorphism arises this way because each coordinate of an
automorphism is a `ℚ`-algebra map `ℚ³ → ℚ`, hence evaluation at a coordinate
(`algHom_eq_eval`, from `SplitAutomorphisms`), and the resulting map of coordinates is
injective. The canonical action is translation, i.e. the subgroup `C₃ ⊂ S₃`.

A transposition `π` of `ZMod 3` is a reflection `h ↦ c - h`, so
`π(h) + g = π(h - g)`: precomposition with `π` turns translation by `g` into
translation by `-g`, which is the twisted action.
-/

noncomputable section

namespace Cubic.OrbitParametrization.C3Algebra

/-- The coordinate permutation `f ↦ f ∘ π⁻¹` of `ℚ³`. -/
def permAlg (π : Equiv.Perm (ZMod 3)) : (ZMod 3 → ℚ) ≃ₐ[ℚ] (ZMod 3 → ℚ) where
  toFun f h := f (π⁻¹ h)
  invFun f h := f (π h)
  left_inv f := by ext h; simp
  right_inv f := by ext h; simp
  map_mul' f g := rfl
  map_add' f g := rfl
  commutes' q := rfl

theorem permAlg_apply (π : Equiv.Perm (ZMod 3)) (f : ZMod 3 → ℚ) (h : ZMod 3) :
    permAlg π f h = f (π⁻¹ h) := rfl

/-- Coordinate permutation as a group homomorphism `S₃ → Aut(ℚ³)`. -/
def permHom : Equiv.Perm (ZMod 3) →* ((ZMod 3 → ℚ) ≃ₐ[ℚ] (ZMod 3 → ℚ)) where
  toFun := permAlg
  map_one' := by ext f h; rfl
  map_mul' π₁ π₂ := by ext f h; rfl

/-- An injective function `ZMod 3 → ℚ`, used to separate coordinates. -/
def coordLabel : ZMod 3 → ℚ := fun j => ((j.val : ℕ) : ℚ)

theorem coordLabel_injective : Function.Injective coordLabel :=
  fun _ _ h => ZMod.val_injective 3 (Nat.cast_injective h)

theorem permHom_bijective : Function.Bijective permHom := by
  constructor
  · intro π π' h
    have h1 : ∀ k, π⁻¹ k = π'⁻¹ k := fun k =>
      coordLabel_injective (congrFun (congrArg (fun τ : (ZMod 3 → ℚ) ≃ₐ[ℚ] (ZMod 3 → ℚ) =>
        τ coordLabel) h) k)
    exact inv_injective (Equiv.ext h1)
  · intro τ
    have hev : ∀ h : ZMod 3, ∃ k : ZMod 3, ∀ f, τ f h = f k := fun h =>
      algHom_eq_eval ((Pi.evalAlgHom ℚ (fun _ => ℚ) h).comp τ.toAlgHom)
    choose k hk using hev
    have hkinj : Function.Injective k := by
      intro h h' hkk
      have e1 := hk h (τ.symm coordLabel)
      have e2 := hk h' (τ.symm coordLabel)
      rw [τ.apply_symm_apply] at e1 e2
      exact coordLabel_injective (by rw [e1, e2, hkk])
    let ρ : Equiv.Perm (ZMod 3) := Equiv.ofBijective k (Finite.injective_iff_bijective.mp hkinj)
    refine ⟨ρ⁻¹, ?_⟩
    ext f h
    change f (ρ⁻¹⁻¹ h) = τ f h
    rw [inv_inv, hk]
    rfl

/-- `S₃ = Aut_{ℚ-alg}(ℚ³)`. -/
def permEquiv : Equiv.Perm (ZMod 3) ≃* ((ZMod 3 → ℚ) ≃ₐ[ℚ] (ZMod 3 → ℚ)) :=
  MulEquiv.ofBijective permHom permHom_bijective

/-- A transposition of `ZMod 3` turns translation by `g` into translation by `-g`. -/
theorem swap_add (a b : ZMod 3) (hab : a ≠ b) (h g : ZMod 3) :
    Equiv.swap a b h + g = Equiv.swap a b (h - g) := by
  revert a b h g
  decide

theorem «example:splitAlgebra» : CubicTargets.OrbitParametrization.SplitAlgebraTwist.Claim := by
  refine ⟨⟨permEquiv, fun π f h => rfl, fun g => ?_⟩, ?_⟩
  · refine AlgEquiv.ext fun f => funext fun h => ?_
    change f (h + Multiplicative.toAdd g) = f ((Equiv.addRight (-Multiplicative.toAdd g))⁻¹ h)
    simp [Equiv.Perm.inv_def]
  · rintro π ⟨a, b, hab, rfl⟩
    refine ⟨permAlg (Equiv.swap a b)⁻¹, fun f h => ?_, fun g y => ?_⟩
    · change f ((Equiv.swap a b)⁻¹⁻¹ h) = f (Equiv.swap a b h)
      rw [inv_inv]
    · refine funext fun h => ?_
      change y ((Equiv.swap a b)⁻¹⁻¹ h + Multiplicative.toAdd g) =
        y ((Equiv.swap a b)⁻¹⁻¹ (h + Multiplicative.toAdd g⁻¹))
      rw [inv_inv, toAdd_inv, ← sub_eq_add_neg, swap_add a b hab]

end Cubic.OrbitParametrization.C3Algebra
