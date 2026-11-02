import Cubic.SantensComparison.PicardLattices

/-! Santens's adelic Picard presentation before deleting any generators.
There are five arithmetic orbit divisors and one real-face divisor. We
quotient by the actual invariant character relation and the three boundary
relations, then identify this quotient with the retained three-divisor
presentation. Boundary-to-face relations have opposite signs: their images
are identified, so the composite in the presentation is zero. -/

noncomputable section

namespace Cubic.SantensComparison.AdelicPicardPresentation

open FanData PicardLattices Cubic.SurfaceGeometry.ResolutionData

def arithmeticPrincipal (a : ℤ) : Fin 5 → ℤ :=
  fun i => pairing (a,a) (orbitRepresentative i)

theorem arithmetic_principal (a : ℤ) : arithmeticPrincipal a = ![-2*a,-a,0,a,a] := by
  ext i
  fin_cases i <;> simp [arithmeticPrincipal, pairing, orbitRepresentative, rays] <;> ring

/-- The first column is the invariant character; the other columns identify
the boundary orbit divisors with their real-face images (zero off the face). -/
def relations : (Fin 4 → ℤ) →ₗ[ℤ] (Fin 6 → ℤ) where
  toFun a := ![arithmeticPrincipal (a 0) 0 + a 1,
    arithmeticPrincipal (a 0) 1 + a 2, arithmeticPrincipal (a 0) 2 + a 3,
    arithmeticPrincipal (a 0) 3, arithmeticPrincipal (a 0) 4, -a 1]
  map_add' a b := by
    ext i
    fin_cases i <;> simp [arithmetic_principal] <;> ring
  map_smul' c a := by
    ext i
    fin_cases i <;> simp [arithmetic_principal] <;> ring

abbrev PresentedPicard := (Fin 6 → ℤ) ⧸ relations.range

def retainedDivisors : (Fin 6 → ℤ) →ₗ[ℤ] (Fin 3 → ℤ) where
  toFun d := ![d 0+d 5,d 3,d 4]
  map_add' d e := by ext i; fin_cases i <;> simp; ring
  map_smul' c d := by ext i; fin_cases i <;> simp; ring

def projection : (Fin 6 → ℤ) →ₗ[ℤ] (ℤ × ℤ) := adelicProjection.comp retainedDivisors

theorem projection_formula (d : Fin 6 → ℤ) :
    projection d=(d 0+d 5+2*d 4,d 3-d 4) := by
  simp [projection, retainedDivisors, adelicProjection]

theorem projection_surjective : Function.Surjective projection := by
  intro m
  exact ⟨![m.1,0,0,m.2,0,0],by simp [projection_formula]⟩

theorem relations_range : relations.range=projection.ker := by
  ext d
  constructor
  · rintro ⟨a,rfl⟩
    rw [LinearMap.mem_ker, projection_formula]
    simp [relations, arithmetic_principal]
  · intro hd
    have h₁ := congrArg Prod.fst (LinearMap.mem_ker.mp hd)
    have h₂ := congrArg Prod.snd (LinearMap.mem_ker.mp hd)
    rw [projection_formula] at h₁ h₂
    change d 0+d 5+2*d 4=0 at h₁
    change d 3-d 4=0 at h₂
    refine ⟨![d 4,-d 5,d 1+d 4,d 2],?_⟩
    ext i
    fin_cases i <;> simp [relations, arithmetic_principal] <;> omega

def presentedEquiv : PresentedPicard ≃ₗ[ℤ] AdelicPicard :=
  ((Submodule.quotEquivOfEq _ _ relations_range).trans
    (projection.quotKerEquivOfSurjective projection_surjective)).trans adelicPicardEquiv.symm

/-- The isomorphism retains exactly the geometric divisor images, rather
than merely comparing the two ranks. -/
theorem presentation_mk (d : Fin 6 → ℤ) :
    presentedEquiv (Submodule.Quotient.mk d)=
      Submodule.Quotient.mk (retainedDivisors d) := by
  apply adelicPicardEquiv.injective
  simp [presentedEquiv, adelic_picard_mk]
  rfl

theorem boundary_relations_vanish :
    (Submodule.Quotient.mk ![1,0,0,0,0,-1] : PresentedPicard)=0 ∧
    (Submodule.Quotient.mk ![0,1,0,0,0,0] : PresentedPicard)=0 ∧
    (Submodule.Quotient.mk ![0,0,1,0,0,0] : PresentedPicard)=0 := by
  refine ⟨?_,?_,?_⟩ <;> apply presentedEquiv.injective <;>
    apply adelicPicardEquiv.injective <;>
    simp [presentation_mk, retainedDivisors, adelic_picard_mk, adelicProjection]

end Cubic.SantensComparison.AdelicPicardPresentation
