import CubicTargets.SantensComparison.SantensInput
import Cubic.SantensComparison.ToricCountingSpecialization
import Cubic.SurfaceGeometry.SurfaceResolvedBoundary
import Cubic.Counting.IntegralPointCount
import CubicTargets.SantensComparison.SantensConstant

/-! `prop:santensConstant`, conditional on the named general literature input.
The proof specializes the actual fan, model, metric and divisor quotients,
then substitutes the computed local integrals. The earlier counting estimate
is not used: IntegralPointCount supplies only its algebraic point equivalence.
-/

noncomputable section

namespace Cubic.SantensComparison.SantensConstant

open ToricMetricData ToricPairApplicability ToricPicardSpecialization
open ToricCountingSpecialization Cubic.Counting.IntegralPointCountData

theorem «prop:santensConstant»
    (hSantens : CubicTargets.SantensComparison.SantensInput.GeneralSantens) :
    CubicTargets.SantensComparison.SantensConstant.Claim := by
  obtain ⟨hfinite,hcount⟩ := hSantens paperPair paperLattices paperModel paperSupport 2 1
    applicability pointed ⟨(1,0),by simpa using height_class⟩
    (by norm_num) anticanonical positive_coefficient
  refine ⟨Cubic.SurfaceGeometry.SurfaceResolvedBoundary.«prop:surfaceResolvedBoundary»,
    PicardLattices.arithmetic_picard_rank,
    ⟨PicardLattices.openPicardEquiv,PicardLattices.open_picard_mk⟩,
    ⟨PicardLattices.adelicPicardEquiv,PicardLattices.adelic_picard_mk⟩,
    FanArithmetic.units,FanArithmetic.regular_functions,FanArithmetic.stable_faces,
    ConeIntegral.cone_constant,?_,?_,?_⟩
  · have hp := TamagawaProduct.positive
    rw [TamagawaProduct.tau_value] at hp
    linarith
  · intro B
    have hf := hfinite B
    rw [paper_bounded_points] at hf
    haveI := hf.to_subtype
    exact Set.finite_coe_iff.mp (Finite.of_equiv _
      (Cubic.Counting.IntegralPointCount.boundedPointsEquiv B))
  · simpa only [paper_count, Cubic.Counting.IntegralPointCount.affineCount_eq,
      coefficient_value, Real.rpow_two] using hcount

end Cubic.SantensComparison.SantensConstant
