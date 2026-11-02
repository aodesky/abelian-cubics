import Cubic.SurfaceGeometry.SymmetricVeroneseGeneration
import Cubic.SurfaceGeometry.SurfaceInvariantRelation
import Cubic.SurfaceGeometry.HomogeneousInvariantPresentation

noncomputable section

namespace Cubic.SurfaceGeometry.ThirdVeroneseGeneration

open MvPolynomial InvariantCubicData VeroneseGrading VeroneseData
open Cubic.ToricHeights.TernaryCyclicInvariants

theorem eliminate_h : e 2 ^ 3 = -delta ^ 2 + (e 1 * e 2 - 3 * e 3) * delta -
    e 1 ^ 3 * e 3 + 6 * e 1 * e 2 * e 3 - 9 * e 3 ^ 2 := by
  have h := SurfaceInvariantRelation.«eqn:surfaceInvariantRelation»
  unfold CubicTargets.SurfaceGeometry.SurfaceInvariantRelation.Claim at h
  linear_combination h

theorem symmetricEval_mem {p : SymmetricCoefficients} (hp : p ∈ symmetricVeronese) :
    symmetricEval p ∈ Algebra.adjoin ℤ cubicGenerators := by
  rw [← SymmetricVeroneseGeneration.generated] at hp
  let S := Algebra.adjoin ℤ cubicGenerators
  have hA : A ∈ S := Algebra.subset_adjoin (by simp [cubicGenerators])
  have hB : B ∈ S := Algebra.subset_adjoin (by simp [cubicGenerators])
  have hC : InvariantCubicData.C ∈ S := Algebra.subset_adjoin (by simp [cubicGenerators])
  have hD : D ∈ S := Algebra.subset_adjoin (by simp [cubicGenerators])
  induction hp using Algebra.adjoin_induction with
  | mem p hp =>
    simp only [symmetricGenerators, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · simpa [symmetricEval, A] using hA
    · simpa [symmetricEval, B] using hB
    · simpa [symmetricEval, InvariantCubicData.C] using hC
    · simp only [map_pow, symmetricEval, aeval_X]
      change e 2 ^ 3 ∈ S
      rw [eliminate_h]
      convert S.sub_mem (S.add_mem
        (S.sub_mem (S.add_mem (S.neg_mem (S.pow_mem hD 2))
          (S.mul_mem (S.sub_mem hB (S.mul_mem (S.algebraMap_mem 3) hC)) hD))
          (S.mul_mem hA hC))
        (S.mul_mem (S.mul_mem (S.algebraMap_mem 6) hB) hC))
        (S.mul_mem (S.algebraMap_mem 9) (S.pow_mem hC 2)) using 1
      dsimp [A, B, InvariantCubicData.C, D]
      simp only [map_ofNat]
      congr 1
      ring
  | algebraMap r => simpa only [AlgHom.commutes] using S.algebraMap_mem r
  | add p q hp hq ihp ihq => simpa only [map_add] using S.add_mem ihp ihq
  | mul p q hp hq ihp ihq => simpa only [map_mul] using S.mul_mem ihp ihq

theorem generators_mem : Algebra.adjoin ℤ cubicGenerators ≤ thirdVeronese := by
  rw [Algebra.adjoin_le_iff]
  intro p hp
  simp only [cubicGenerators, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  have he (i : Fin 3) : e (i.val + 1) ∈ invariants := by
    exact (esymm_isSymmetric (Fin 3) ℤ (i.val + 1)) (finRotate 3)
  rcases hp with rfl | rfl | rfl | rfl
  · exact ⟨invariants.pow_mem (he 0) 3, (e_homogeneous 0).pow 3⟩
  · exact ⟨invariants.mul_mem (he 0) (he 1), (e_homogeneous 0).mul (e_homogeneous 1)⟩
  · exact ⟨he 2, e_homogeneous 2⟩
  · exact ⟨Cubic.ToricHeights.CyclicSymmetricDecomposition.rename_cycle_delta,
      delta_homogeneous⟩

theorem generated : Algebra.adjoin ℤ cubicGenerators = thirdVeronese := by
  apply le_antisymm generators_mem
  intro p hp
  obtain ⟨⟨a,b⟩,hab,_⟩ := IntegralInvariantNormalForm.exists_unique_normalForm p hp.1
  have hw : IsWeightedHomogeneous ordinaryWeight (normalForm (a,b)) 0 := hab.symm ▸ hp.2
  obtain ⟨ha,hb⟩ := (normalForm_homogeneous_iff (a,b)).mp hw
  rw [← hab]
  exact (Algebra.adjoin ℤ cubicGenerators).add_mem (symmetricEval_mem ha)
    ((Algebra.adjoin ℤ cubicGenerators).mul_mem (symmetricEval_mem hb)
      (Algebra.subset_adjoin (by simp [cubicGenerators, D])))

end Cubic.SurfaceGeometry.ThirdVeroneseGeneration
