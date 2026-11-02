import Cubic.OrbitParametrization.C3Algebra
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.NumberTheory.NumberField.Basic

/-! For a finite constant group, continuous Galois cocycles are
homomorphisms with open kernel, and cohomology is conjugacy.
The cocycle below is the actual restriction map of a number field
embedded in the algebraic closure of `ℚ`. -/

noncomputable section

namespace Cubic.OrbitParametrization.TwistCohomologyData

open C3Algebra

abbrev AbsoluteGroup := AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

variable (K : Type) [Field K] [NumberField K]

def embedding : K →ₐ[ℚ] AlgebraicClosure ℚ := IsAlgClosed.lift
def imageField : IntermediateField ℚ (AlgebraicClosure ℚ) := (embedding K).fieldRange

def imageEquiv : K ≃ₐ[ℚ] imageField K :=
  AlgEquiv.ofInjective (embedding K) (embedding K).injective

instance : FiniteDimensional ℚ (imageField K) :=
  Module.Finite.equiv (imageEquiv K).toLinearEquiv

instance [IsGalois ℚ K] : IsGalois ℚ (imageField K) :=
  IsGalois.of_algEquiv (imageEquiv K)

def restriction [IsGalois ℚ K] : AbsoluteGroup →* (K ≃ₐ[ℚ] K) :=
  (imageEquiv K).symm.autCongr.toMonoidHom.comp (AlgEquiv.restrictNormalHom (imageField K))

def fieldCocycle [IsGalois ℚ K] (ι : C3 ≃* (K ≃ₐ[ℚ] K)) : AbsoluteGroup →* C3 :=
  ι.symm.toMonoidHom.comp (restriction K)

variable {K}

def inverseCocycle (c : AbsoluteGroup →* C3) : AbsoluteGroup →* C3 :=
  (invMonoidHom (α := C3)).comp c

/-- Conjugacy is the equivalence relation defining `H¹` for a constant group. -/
def Cohomologous {G : Type*} [Group G] (c d : AbsoluteGroup →* G) : Prop :=
  ∃ a : G, ∀ τ, d τ = a * c τ * a⁻¹

/-- The inclusion `C₃ ↪ S₃` by its regular action on its three elements. -/
def regular : C3 →* Equiv.Perm C3 where
  toFun := Equiv.mulLeft
  map_one' := by ext x; simp
  map_mul' a b := by ext x; simp [mul_assoc]

/-- The cohomology footnote, including the arithmetic restriction map and
its continuity (open kernel) for the actual field in the example. -/
def Claim : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsGalois ℚ K],
    ∀ ι : C3 ≃* (K ≃ₐ[ℚ] K),
      Function.Surjective (fieldCocycle K ι) ∧
      IsOpen ((fieldCocycle K ι).ker : Set AbsoluteGroup) ∧
      (∀ τ y, embedding K ((restriction K τ) y) = τ (embedding K y)) ∧
      (∀ τ, ι (inverseCocycle (fieldCocycle K ι) τ) = (restriction K τ)⁻¹) ∧
      ¬ Cohomologous (fieldCocycle K ι) (inverseCocycle (fieldCocycle K ι)) ∧
      Cohomologous (regular.comp (fieldCocycle K ι))
        (regular.comp (inverseCocycle (fieldCocycle K ι)))

end Cubic.OrbitParametrization.TwistCohomologyData
