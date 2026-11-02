import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Data.Set.Finite.Lattice

/-! A basis for finitely supported coefficient functions constant on finite
fibers. Applied to monomial orbits, its vectors are orbit sums with coefficient
one, so the construction works over every coefficient ring. -/

noncomputable section

namespace Cubic.SurfaceGeometry.OrbitCoefficientBasis

variable {α β : Type*} (R : Type*) [CommRing R] (p : α → β)

def constantOnFibres : Submodule R (α →₀ R) where
  carrier := {f | ∀ a b, p a = p b → f a = f b}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg a b hab
    simp only [Finsupp.add_apply, hf a b hab, hg a b hab]
  smul_mem' := by
    intro r f hf a b hab
    simp only [Finsupp.smul_apply, hf a b hab]

variable (hp : Function.Surjective p) (hfin : ∀ b, (p ⁻¹' {b}).Finite)

def inflate (f : β →₀ R) : α →₀ R :=
  Finsupp.ofSupportFinite (fun a => f (p a))
    (f.finite_support.preimage' (fun b _ => hfin b))

@[simp] theorem inflate_apply (f : β →₀ R) (a : α) :
    inflate R p hfin f a = f (p a) := rfl

def inflateLinear : (β →₀ R) →ₗ[R] constantOnFibres R p where
  toFun f := ⟨inflate R p hfin f, fun a b hab => by simp [hab]⟩
  map_add' := by intro f g; apply Subtype.ext; ext a; rfl
  map_smul' := by intro r f; apply Subtype.ext; ext a; rfl

def coefficients : constantOnFibres R p →ₗ[R] (β →₀ R) :=
  (Finsupp.lcomapDomain (Function.surjInv hp) (Function.injective_surjInv hp)).comp
    (constantOnFibres R p).subtype

@[simp] theorem coefficients_apply (f : constantOnFibres R p) (b : β) :
    coefficients R p hp f b = f.val (Function.surjInv hp b) := rfl

def repr : constantOnFibres R p ≃ₗ[R] (β →₀ R) :=
  LinearEquiv.ofLinear (coefficients R p hp) (inflateLinear R p hfin)
    (by
      apply LinearMap.ext
      intro f
      ext b
      change f (p (Function.surjInv hp b)) = f b
      rw [Function.surjInv_eq hp b])
    (by
      apply LinearMap.ext
      intro f
      apply Subtype.ext
      ext a
      change f.val (Function.surjInv hp (p a)) = f.val a
      exact f.property _ _ (Function.surjInv_eq hp (p a)))

def basis : Module.Basis β R (constantOnFibres R p) :=
  Module.Basis.ofRepr (repr R p hp hfin)

open scoped Classical in
/-- The vector indexed by a fiber has coefficient one precisely on that fiber. -/
theorem basis_apply (b : β) (a : α) :
    (basis R p hp hfin b).val a = if p a = b then 1 else 0 := by
  classical
  change (Finsupp.single b (1 : R)) (p a) = _
  simp only [Finsupp.single_apply, eq_comm]

end Cubic.SurfaceGeometry.OrbitCoefficientBasis
