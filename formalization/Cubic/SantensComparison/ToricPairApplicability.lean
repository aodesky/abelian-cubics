import Cubic.SantensComparison.ToricPairData
import Cubic.SantensComparison.AdelicPicardPresentation

/-! Instantiation of the general fan, model and metric conditions by the
paper's original cubic quotient and its minimal resolution. -/

noncomputable section

namespace Cubic.SantensComparison.ToricPairApplicability

open ToricPairData ToricFanData ToricMetricData
open Cubic.SurfaceGeometry.ResolutionData

def paperPair : Pair where
  fan := paperFan
  conjugate := FanData.conjugateRay
  boundary := ({0,1,2,7,8} : Finset (Fin 9))
  realFace := (0 : Fin 9)
  openSize := 4
  openRay := FanData.openRay
  openConjugate := FanData.openConjugation
  orbitSize := 3
  orbitRay := FanData.adelicRay

theorem boundary_mem (i : Fin 9) : i ∈ paperPair.boundary ↔ boundary i=1 := by
  fin_cases i <;> decide

theorem boundary_not_mem (i : Fin 9) : i ∉ paperPair.boundary ↔ boundary i=0 := by
  fin_cases i <;> decide

theorem stable_faces (A : Finset (Fin 9)) :
    paperPair.StableFace A ↔ FanData.StableFace A := by
  constructor
  · rintro ⟨⟨hb,j,hj⟩,hc⟩
    refine ⟨⟨fun i hi => (boundary_mem i).mp (hb i hi),j,?_⟩,
      fun i => ⟨hc i,?_⟩⟩
    · intro i hi
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hj i hi
    · intro hi
      have hh : FanData.conjugateRay (FanData.conjugateRay i) ∈ A :=
        hc (FanData.conjugateRay i) hi
      rwa [FanArithmetic.conjugation_involutive i] at hh
  · rintro ⟨⟨hb,j,hj⟩,hc⟩
    refine ⟨⟨fun i hi => (boundary_mem i).mpr (hb i hi),j,?_⟩,
      fun i hi => (hc i).mp hi⟩
    intro i hi
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hj hi

theorem paper_laws : paperPair.Laws where
  smooth_complete := paper_smooth_complete
  conjugate_involutive := FanArithmetic.conjugation_involutive
  conjugate_ray := FanArithmetic.conjugate_ray
  conjugate_next := by intro i; fin_cases i <;> decide
  boundary_stable := by intro i; fin_cases i <;> decide
  open_exact := by intro i; fin_cases i <;> unfold ExistsUnique <;> decide
  open_conjugate := FanArithmetic.open_conjugation
  open_conjugate_involutive := by intro i; fin_cases i <;> decide
  orbit_retained := by intro i; fin_cases i <;> unfold Pair.Retained <;> decide
  orbit_exact := by intro i; fin_cases i <;> unfold Pair.Retained ExistsUnique <;> decide
  face_boundary := by decide
  face_ray := by decide
  real_faces A := (stable_faces A).trans (FanArithmetic.stable_faces A)

theorem paper_open_characters : paperPair.openCharacters=RegularFunctions.openCharacters := rfl

theorem paper_cone_algebra : paperPair.coneAlgebra=AffineConeAlgebra.coneAlgebra := rfl

theorem paper_open_support : paperPair.openSupport=OpenFanProperness.affineCone := by
  unfold Pair.openSupport
  have hs : {i : Fin 9 | i ∉ paperPair.boundary ∧ paperPair.fan.next i ∉ paperPair.boundary}=
      {i : Fin 9 | boundary i=0 ∧ boundary (next i)=0} := by
    ext i
    change (i ∉ paperPair.boundary ∧ next i ∉ paperPair.boundary) ↔ _
    simp only [Set.mem_setOf_eq, boundary_not_mem]
  change (⋃ i : {i : Fin 9 | i ∉ paperPair.boundary ∧
      paperPair.fan.next i ∉ paperPair.boundary}, OpenFanProperness.cone i.val)=_
  rw [hs]
  exact OpenFanProperness.proper_support

theorem applicability : paperPair.Applicability paperModel paperSupport where
  fan_laws := paper_laws
  metric := ToricMetricGeometry.paper_metric
  finite_generation := AffineConeAlgebra.paperModel_finite_generation
  generic_fibre := AffineConeAlgebra.generic_fibre
  proper_support := by
    refine ⟨(3:Fin 9),(6:Fin 9),?_,paper_open_support⟩
    simp only [paperPair]
    norm_num [Fan.realRay, paper_ray, rays, detReal]
  pure_open := by intro i; fin_cases i <;> decide
  constant_units := FanArithmetic.units
  no_obstruction := FanArithmetic.regular_functions

/-- The general cokernels specialize to the actual divisor quotients
already used in the integral lattice and Galois-action computations. -/
def openPicardEquiv : paperPair.OpenPicard ≃ₗ[ℤ] FanData.OpenPicard := LinearEquiv.refl ℤ _

def adelicPicardEquiv : paperPair.AdelicPicard ≃ₗ[ℤ] FanData.AdelicPicard :=
  LinearEquiv.refl ℤ _

end Cubic.SantensComparison.ToricPairApplicability
