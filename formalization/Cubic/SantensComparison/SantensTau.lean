import CubicTargets.SantensComparison.SantensTau
import Cubic.SantensComparison.ToricCountingSpecialization

/-! Exact-label proof of the constant decomposition in `eqn:santensTau`. -/

namespace Cubic.SantensComparison.SantensTau
open ToricCountingData ToricPicardSpecialization

theorem «eqn:santensTau» : CubicTargets.SantensComparison.SantensTau.Claim := by
  refine ⟨?_, rfl, ?_, ?_⟩
  · rw [coefficient, ToricPicardSpecialization.theta, ConeIntegral.cone_constant]
    norm_num
  · simp_rw [ToricCountingSpecialization.split_volume]
    exact TamagawaProduct.split_absolute
  · simp_rw [ToricCountingSpecialization.inert_volume]
    exact TamagawaProduct.inert_absolute
end Cubic.SantensComparison.SantensTau
