import Cubic.SantensComparison.ToricPicardData
import Cubic.SantensComparison.ToricPairApplicability
import Cubic.SantensComparison.ConeIntegral

noncomputable section

namespace Cubic.SantensComparison.ToricPicardSpecialization

open ToricPairData ToricPicardData ToricPairApplicability ToricMetricData
open Cubic.SurfaceGeometry.ResolutionData

def paperLattices : Lattices paperPair where
  openBasis := openPicardEquiv.trans PicardLattices.openPicardEquiv
  adelicBasis := adelicPicardEquiv.trans PicardLattices.adelicPicardEquiv
  permutation := PicardLattices.open_picard_conjugation

theorem generators (i : Fin 3) :
    paperLattices.generator i = ![(1,0),(0,1),(2,-1)] i := by
  change (((PicardLattices.adelicPicardEquiv
      (Submodule.Quotient.mk (Pi.single i 1))).1 : ℝ),
    ((PicardLattices.adelicPicardEquiv
      (Submodule.Quotient.mk (Pi.single i 1))).2 : ℝ)) = _
  rw [PicardLattices.adelic_picard_mk]
  fin_cases i <;> norm_num [FanData.adelicProjection, Pi.single_apply] <;> decide

theorem height_class : paperLattices.heightClass paperSupport=(1,0) := by
  unfold Lattices.heightClass
  change (∑ i : Fin 3, (paperSupport (ToricMetricGeometry.ambientCoordinates
    (ToricFanData.paperFan.realRay (FanData.adelicRay i)))).re • paperLattices.generator i)=_
  have hv (i : Fin 3) : (paperSupport (ToricMetricGeometry.ambientCoordinates
      (ToricFanData.paperFan.realRay (FanData.adelicRay i)))).re =
        if i=0 then 1 else 0 := by
    fin_cases i <;>
      norm_num [paperSupport, Cubic.ToricHeights.supportFunction,
        ToricMetricGeometry.ambientCoordinates, ToricFanData.Fan.realRay,
        ToricFanData.paper_ray, FanData.adelicRay, rays]
  simp [hv, ite_smul, generators]

theorem effective_cone : paperLattices.effectiveCone=FanData.effectiveCone := by
  ext x
  rw [ConeIntegral.effective_cone]
  change (∃ c : Fin 3 → ℝ, (∀ i, 0 ≤ c i) ∧
    (∀ i, FanData.adelicRay i ∈ paperPair.boundary → c i=0) ∧
      x=∑ i, c i • paperLattices.generator i) ↔ _
  constructor
  · rintro ⟨c,hc,hb,rfl⟩
    have h₀ : c (0:Fin 3)=0 := hb 0 (by decide)
    refine ⟨c 1,c 2,hc 1,hc 2,?_⟩
    change (∑ i : Fin 3, c i • paperLattices.generator i)=_
    rw [Fin.sum_univ_three, h₀]
    simp [generators, Prod.smul_mk, smul_eq_mul, mul_comm, sub_eq_add_neg]
  · rintro ⟨a,b,ha,hb,rfl⟩
    refine ⟨![0,a,b],?_,?_,?_⟩
    · intro i; fin_cases i <;> simp [ha,hb]
    · intro i
      rw [boundary_mem]
      fin_cases i <;> norm_num [boundary, FanData.adelicRay]
    · change (2*b,a-b) = ∑ i : Fin 3, ![0,a,b] i • paperLattices.generator i
      rw [Fin.sum_univ_three]
      simp [generators, Prod.smul_mk, smul_eq_mul, mul_comm, sub_eq_add_neg]

theorem dual_cone : paperLattices.dualCone=FanData.dualCone := by
  unfold Lattices.dualCone FanData.dualCone
  rw [effective_cone]

theorem theta : paperLattices.theta paperSupport=FanData.theta := by
  simp only [Lattices.theta, height_class, dual_cone, one_mul, zero_mul, add_zero]
  rfl

theorem pointed : paperLattices.Pointed := by
  intro x hx hn
  rw [effective_cone, ConeIntegral.effective_cone] at hx hn
  obtain ⟨a,b,ha,hb,hx⟩ := hx
  obtain ⟨c,d,hc,hd,hn⟩ := hn
  have h₁ := congrArg Prod.fst hx
  have h₂ := congrArg Prod.snd hx
  have h₃ := congrArg Prod.fst hn
  have h₄ := congrArg Prod.snd hn
  apply Prod.ext <;> dsimp at * <;> linarith

theorem anticanonical : Lattices.Anticanonical paperPair paperSupport 2 1 := by
  intro i hi
  have h := ToricMetricGeometry.paper_log_anticanonical i
  have hi' : boundary i=0 ∨ i=(0:Fin 9) := by
    rcases hi with hi | hi
    · exact Or.inl ((boundary_not_mem i).mp hi)
    · exact Or.inr hi
  have he := h hi'
  have hb : (if i ∈ paperPair.boundary then 0 else 1 : ℝ) = antiK i-boundary i := by
    by_cases hi : i ∈ paperPair.boundary
    · rw [if_pos hi, (boundary_mem i).mp hi]
      norm_num [antiK]
    · rw [if_neg hi, (boundary_not_mem i).mp hi]
      norm_num [antiK]
  rw [hb]
  exact he

end Cubic.SantensComparison.ToricPicardSpecialization
