import Cubic.SantensComparison.FanArithmetic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.Nilpotent

/-! The actual toric regular-function algebras, obtained by intersecting the
dual semigroups of the retained rays. Character inequalities imply statements
about every regular function and every invertible regular function. -/

noncomputable section

namespace Cubic.SantensComparison.RegularFunctions

open FanData Cubic.SurfaceGeometry.ResolutionData

def openCharacters : AddSubmonoid (ℤ × ℤ) where
  carrier := {m | ∀ i, 0 ≤ pairing m (openRay i)}
  zero_mem' := by simp [pairing]
  add_mem' := by
    intro a b ha hb i
    have h₁ := ha i
    have h₂ := hb i
    dsimp [pairing] at *
    nlinarith

def adelicCharacters : AddSubmonoid (ℤ × ℤ) where
  carrier := {m | m ∈ openCharacters ∧ 0 ≤ pairing m 0}
  zero_mem' := ⟨openCharacters.zero_mem,by simp [pairing]⟩
  add_mem' := by
    rintro a b ⟨ha,h₀a⟩ ⟨hb,h₀b⟩
    refine ⟨openCharacters.add_mem ha hb,?_⟩
    dsimp [pairing] at *
    nlinarith

theorem nonnegative_coordinates (m : openCharacters) : 0 ≤ m.val.1 ∧ 0 ≤ m.val.2 := by
  have h₁ := m.property 2
  have h₂ := m.property 3
  simpa [pairing, openRay, rays] using And.intro h₁ h₂

def polynomialExponent : openCharacters →+ (Fin 2 →₀ ℕ) where
  toFun m := Finsupp.equivFunOnFinite.symm ![m.val.1.toNat,m.val.2.toNat]
  map_zero' := by ext i; fin_cases i <;> simp
  map_add' m n := by
    ext i
    fin_cases i <;> simp [Int.toNat_add (nonnegative_coordinates m).1
      (nonnegative_coordinates n).1, Int.toNat_add (nonnegative_coordinates m).2
        (nonnegative_coordinates n).2]

theorem polynomialExponent_injective : Function.Injective polynomialExponent := by
  intro m n h
  have h₁ := DFunLike.congr_fun h 0
  have h₂ := DFunLike.congr_fun h 1
  simp [polynomialExponent] at h₁ h₂
  have hm := nonnegative_coordinates m
  have hn := nonnegative_coordinates n
  apply Subtype.ext
  apply Prod.ext <;> omega

variable (k : Type*) [Field k]

def openPolynomial : AddMonoidAlgebra k openCharacters →ₐ[k] MvPolynomial (Fin 2) k :=
  AddMonoidAlgebra.mapDomainAlgHom k k polynomialExponent

theorem openPolynomial_injective : Function.Injective (openPolynomial k) :=
  Finsupp.mapDomain_injective polynomialExponent_injective

theorem invertible_functions (f : AddMonoidAlgebra k openCharacters) (hf : IsUnit f) :
    ∃ c : kˣ, f=algebraMap k _ c := by
  obtain ⟨r,⟨c,hc⟩,hp⟩ :=
    MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp (hf.map (openPolynomial k))
  refine ⟨c,?_⟩
  apply openPolynomial_injective k
  rw [AlgHom.commutes, hp, ← hc]
  rfl

instance : Unique adelicCharacters where
  default := 0
  uniq m := by
    apply Subtype.ext
    exact FanArithmetic.regular_functions m.val m.property.1 m.property.2

def adelicRegularEquiv : AddMonoidAlgebra k adelicCharacters ≃ₐ[k] k :=
  AddMonoidAlgebra.uniqueAlgEquiv k adelicCharacters

theorem no_analytic_obstruction (f : AddMonoidAlgebra k adelicCharacters) :
    ∃ c : k, f=algebraMap k _ c := by
  refine ⟨adelicRegularEquiv k f,?_⟩
  apply (adelicRegularEquiv k).injective
  rw [AlgEquiv.commutes]
  rfl

end Cubic.SantensComparison.RegularFunctions
