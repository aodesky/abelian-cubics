import Cubic.OrbitParametrization.ModuliMap

/-!
# The split `C₃`-algebra `ℚ³`

The split algebra is `ZMod 3 → ℚ` with `g` acting by translation,
`(g f)(h) = f(h+g)` ([O'Desky–Rosen, proof of Prop. 2.5]). Evaluation at the
coordinate `0` is a `ℚ`-algebra map to `ℚ`; it carries the unit of a pair to the
unit with coefficients `x(-i)`.
-/

noncomputable section

namespace Cubic.OrbitParametrization.C3Algebra

open CyclicGroupAlgebra

/-- Translation by `a` as a `ℚ`-algebra automorphism of `ℚ³`. -/
def shift (a : ZMod 3) : (ZMod 3 → ℚ) ≃ₐ[ℚ] (ZMod 3 → ℚ) where
  toFun f h := f (h + a)
  invFun f h := f (h - a)
  left_inv f := by ext h; simp
  right_inv f := by ext h; simp
  map_mul' f g := rfl
  map_add' f g := rfl
  commutes' q := rfl

/-- The cyclic action on `ℚ³`. -/
def splitAct : C3 →* ((ZMod 3 → ℚ) ≃ₐ[ℚ] (ZMod 3 → ℚ)) where
  toFun g := shift (Multiplicative.toAdd g)
  map_one' := by ext f h; simp [shift]
  map_mul' g g' := by
    ext f h
    change f (h + (Multiplicative.toAdd g + Multiplicative.toAdd g')) =
      f (h + Multiplicative.toAdd g + Multiplicative.toAdd g')
    congr 1
    abel

/-- The split `C₃`-algebra. -/
def splitAlg : C3Alg where
  carrier := ZMod 3 → ℚ
  act := splitAct
  model := Or.inr ⟨AlgEquiv.refl, fun _ _ _ => rfl⟩

/-- Evaluation at the coordinate `0`. -/
def evalZero : (ZMod 3 → ℚ) →ₐ[ℚ] ℚ := Pi.evalAlgHom ℚ (fun _ : ZMod 3 => ℚ) 0

end Cubic.OrbitParametrization.C3Algebra
