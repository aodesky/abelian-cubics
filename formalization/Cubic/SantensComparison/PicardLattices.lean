import Cubic.SantensComparison.FanArithmetic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

noncomputable section

namespace Cubic.SantensComparison.PicardLattices

open FanData Cubic.SurfaceGeometry.ResolutionData

theorem open_principal_formula (m : ℤ × ℤ) :
    openPrincipal m = ![2*m.1-m.2, -m.1+2*m.2, m.1, m.2] := by
  ext i
  fin_cases i <;> simp [openPrincipal, pairing, openRay, rays] <;> ring

theorem open_projection_surjective : Function.Surjective openProjection := by
  intro m
  exact ⟨![m.1,m.2,0,0], by simp [openProjection]⟩

theorem open_principal_range : openPrincipal.range = openProjection.ker := by
  ext d
  constructor
  · rintro ⟨m, rfl⟩
    rw [LinearMap.mem_ker, open_principal_formula]
    ext <;> simp [openProjection]
  · intro hd
    have h₁ := congrArg Prod.fst (LinearMap.mem_ker.mp hd)
    have h₂ := congrArg Prod.snd (LinearMap.mem_ker.mp hd)
    simp [openProjection] at h₁ h₂
    refine ⟨(d 2,d 3), ?_⟩
    rw [open_principal_formula]
    ext i
    fin_cases i <;> simp <;> omega

def openPicardEquiv : OpenPicard ≃ₗ[ℤ] (ℤ × ℤ) :=
  (Submodule.quotEquivOfEq _ _ open_principal_range).trans
    (openProjection.quotKerEquivOfSurjective open_projection_surjective)

theorem open_picard_mk (d : Fin 4 → ℤ) :
    openPicardEquiv (Submodule.Quotient.mk d) = openProjection d := rfl

/-- This is the actual action induced from the four ray divisors, rather
than an independently chosen action on an abstract rank-two group. -/
theorem open_picard_conjugation (d : Fin 4 → ℤ) :
    openPicardEquiv (Submodule.Quotient.mk (conjugateOpenDivisor d)) =
      ((openPicardEquiv (Submodule.Quotient.mk d)).2,
        (openPicardEquiv (Submodule.Quotient.mk d)).1) := by
  simp [open_picard_mk, openProjection, conjugateOpenDivisor, openConjugation]
  constructor <;> ring

/-- The cyclic cocycle relation for the permutation module has only
coboundaries: `ker(1+σ)=im(σ-1)` over the integral lattice. -/
theorem permutation_cocycles (m : ℤ × ℤ) :
    m + (m.2,m.1) = 0 ↔ ∃ n : ℤ × ℤ, m = (n.2,n.1) - n := by
  constructor
  · intro h
    have h₁ := congrArg Prod.fst h
    change m.1 + m.2 = 0 at h₁
    refine ⟨(0,m.1), ?_⟩
    apply Prod.ext <;> dsimp <;> omega
  · rintro ⟨n,rfl⟩
    ext <;> simp

theorem invariant_principal_injective : Function.Injective invariantPrincipal := by
  intro a b h
  have hh := congrFun h 3
  norm_num [invariantPrincipal, orbitRepresentative, rays] at hh
  exact hh

theorem arithmetic_picard_rank : Module.finrank ℚ ArithmeticPicard = 4 := by
  have hr := LinearMap.finrank_range_of_inj invariant_principal_injective
  have hd := Submodule.finrank_quotient_add_finrank invariantPrincipal.range
  rw [hr] at hd
  norm_num [Module.finrank_pi] at hd
  change Module.finrank ℚ ArithmeticPicard + 1 = 5 at hd
  omega

theorem adelic_principal_formula (a : ℤ) : adelicPrincipal a = ![-2*a,a,a] := by
  ext i
  fin_cases i <;> simp [adelicPrincipal, pairing, adelicRay, rays] <;> ring

theorem adelic_projection_surjective : Function.Surjective adelicProjection := by
  intro m
  exact ⟨![m.1,m.2,0], by simp [adelicProjection]⟩

theorem adelic_principal_range : adelicPrincipal.range = adelicProjection.ker := by
  ext d
  constructor
  · rintro ⟨a,rfl⟩
    rw [LinearMap.mem_ker, adelic_principal_formula]
    ext <;> simp [adelicProjection]
  · intro hd
    have h₁ := congrArg Prod.fst (LinearMap.mem_ker.mp hd)
    have h₂ := congrArg Prod.snd (LinearMap.mem_ker.mp hd)
    simp [adelicProjection] at h₁ h₂
    refine ⟨d 2, ?_⟩
    rw [adelic_principal_formula]
    ext i
    fin_cases i <;> simp <;> omega

def adelicPicardEquiv : AdelicPicard ≃ₗ[ℤ] (ℤ × ℤ) :=
  (Submodule.quotEquivOfEq _ _ adelic_principal_range).trans
    (adelicProjection.quotKerEquivOfSurjective adelic_projection_surjective)

theorem adelic_picard_mk (d : Fin 3 → ℤ) :
    adelicPicardEquiv (Submodule.Quotient.mk d) = adelicProjection d := rfl

theorem adelic_basis :
    adelicPicardEquiv (Submodule.Quotient.mk ![1,0,0]) = (1,0) ∧
    adelicPicardEquiv (Submodule.Quotient.mk ![0,1,0]) = (0,1) ∧
    adelicPicardEquiv (Submodule.Quotient.mk ![0,0,1]) = (2,-1) := by
  simp [adelic_picard_mk, adelicProjection]

theorem anticanonical_class :
    adelicPicardEquiv (Submodule.Quotient.mk ![0,1,1]) =
      2 • adelicPicardEquiv (Submodule.Quotient.mk ![1,0,0]) := by
  simp [adelic_picard_mk, adelicProjection]

theorem adelic_picard_rank : Module.finrank ℤ AdelicPicard = 2 := by
  rw [adelicPicardEquiv.finrank_eq]
  simp [Module.finrank_prod]

/-- Restrict the actual pulled-back divisor to the retained orbit divisors. -/
theorem height_class :
    adelicPicardEquiv (Submodule.Quotient.mk
      ![pullbackThreeD0 0,pullbackThreeD0 3,pullbackThreeD0 4]) =
        3 • adelicPicardEquiv (Submodule.Quotient.mk ![1,0,0]) := by
  norm_num [adelic_picard_mk, adelicProjection, pullbackThreeD0, rays]
  decide

theorem log_anticanonical_class :
    adelicPicardEquiv (Submodule.Quotient.mk ![logDivisor 0,logDivisor 3,logDivisor 4]) =
      2 • adelicPicardEquiv (Submodule.Quotient.mk ![1,0,0]) := by
  norm_num [adelic_picard_mk, adelicProjection, logDivisor, antiK, boundary]
  decide

end Cubic.SantensComparison.PicardLattices
