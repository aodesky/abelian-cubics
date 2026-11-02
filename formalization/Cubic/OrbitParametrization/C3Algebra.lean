import Cubic.OrbitParametrization.CyclicGroupAlgebra
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# `C₃`-algebras with a trace-one normal element

The introduction of the paper defines a `C₃`-algebra `K/ℚ` as a `ℚ`-algebra with
a `C₃`-action admitting a `C₃`-linear `ℚ`-algebra isomorphism to a cubic abelian
number field or to the split algebra `ℚ³`. In the field case we transport the
action: `K` is itself a field of degree three on which `C₃` acts faithfully by
`ℚ`-algebra automorphisms (such a field is Galois with group `C₃`, i.e. a cubic
abelian number field). In the split case the model is `ZMod 3 → ℚ`, on which
`g` acts by translation, `(g f)(h) = f(h+g)`, as in [O'Desky–Rosen, §2].

An element `x` is normal if its conjugates are linearly independent over `ℚ`,
and has trace one if they sum to one. Pairs are equivalent if a
`C₃`-equivariant `ℚ`-algebra isomorphism carries one element to the other.
-/

noncomputable section

namespace Cubic.OrbitParametrization.C3Algebra

/-- The cyclic group of order three, written multiplicatively. -/
abbrev C3 := Multiplicative (ZMod 3)

/-- A `C₃`-algebra over `ℚ`, bundled with its carrier. -/
structure C3Alg where
  carrier : Type
  [commRing : CommRing carrier]
  [algebra : Algebra ℚ carrier]
  act : C3 →* (carrier ≃ₐ[ℚ] carrier)
  model : (IsField carrier ∧ Module.finrank ℚ carrier = 3 ∧ Function.Injective act) ∨
    ∃ e : carrier ≃ₐ[ℚ] (ZMod 3 → ℚ), ∀ (g : C3) (y : carrier) (h : ZMod 3),
      e (act g y) h = e y (h + Multiplicative.toAdd g)

attribute [instance] C3Alg.commRing C3Alg.algebra

variable (K : C3Alg)

/-- The conjugates of an element form a basis of `K` over `ℚ`. -/
def IsNormal (x : K.carrier) : Prop := LinearIndependent ℚ (fun g : C3 => K.act g x)

/-- The conjugates of an element sum to one. -/
def HasTraceOne (x : K.carrier) : Prop := ∑ g : C3, K.act g x = 1

/-- A `C₃`-algebra with a trace-one normal element. -/
structure Pair where
  algebra : C3Alg
  element : algebra.carrier
  normal : IsNormal algebra element
  traceOne : HasTraceOne algebra element

/-- Equivalence of pairs: a `C₃`-equivariant `ℚ`-algebra isomorphism matching the elements. -/
def Equivalent (p q : Pair) : Prop :=
  ∃ e : p.algebra.carrier ≃ₐ[ℚ] q.algebra.carrier,
    (∀ (g : C3) (y : p.algebra.carrier), e (p.algebra.act g y) = q.algebra.act g (e y)) ∧
      e p.element = q.element

end Cubic.OrbitParametrization.C3Algebra
