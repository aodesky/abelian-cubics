import CubicTargets.SantensComparison.SantensInput
import Cubic.SantensComparison.ToricCountingSpecialization
import Cubic.SantensComparison.TrivialFiniteMetric
import Cubic.SurfaceGeometry.SurfaceResolvedBoundary
import Cubic.Counting.IntegralPointCount
import CubicTargets.SantensComparison.SantensConstant

/-! `prop:santensConstant`, conditional on the named general literature input.
The proof specializes the actual fan, model, metric and divisor quotients,
then substitutes the computed local integrals. The earlier counting estimate
is not used: IntegralPointCount supplies only its algebraic point equivalence.

As in the paper, the input is applied to the Santens height `H̃` with the
trivial metric at every prime (`TrivialFiniteMetric`). It equals `H(·,1)` on
integral points and in the finite local integrals, so the count and constant
are transported to `H(·,1)`.
-/

noncomputable section

namespace Cubic.SantensComparison.SantensConstant

open ToricMetricData ToricPairApplicability ToricPicardSpecialization
open ToricCountingSpecialization Cubic.Counting.IntegralPointCountData TrivialFiniteMetric

theorem «prop:santensConstant»
    (hSantens : CubicTargets.SantensComparison.SantensInput.GeneralSantens) :
    CubicTargets.SantensComparison.SantensConstant.Claim := by
  -- Santens's theorem for `H̃`, whose finite metrics are trivial.
  obtain ⟨hfinite,hcount⟩ := hSantens paperPair paperLattices paperModel paperSupport
    trivialMetric 2 1 applicability finite_metric pointed ⟨(1,0),by simpa using height_class⟩
    (by norm_num) anticanonical (by rw [coefficient_eq]; exact positive_coefficient)
  -- `H̃=H(·,1)` on the support of the integral weight.
  simp only [count_eq, coefficient_eq] at hcount
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
    rw [bounded_points, paper_bounded_points] at hf
    haveI := hf.to_subtype
    exact Set.finite_coe_iff.mp (Finite.of_equiv _
      (Cubic.Counting.IntegralPointCount.boundedPointsEquiv B))
  · simpa only [paper_count, Cubic.Counting.IntegralPointCount.affineCount_eq,
      coefficient_value, Real.rpow_two] using hcount

end Cubic.SantensComparison.SantensConstant
