import Cubic.SantensComparison.ToricCountingData
import Cubic.SantensComparison.ToricPicardSpecialization
import Cubic.SantensComparison.TamagawaProduct

noncomputable section

namespace Cubic.SantensComparison.ToricCountingSpecialization

open ToricMetricData ToricCountingData ToricPicardSpecialization
open Cubic.PoissonSummation.FiniteEulerProduct

theorem split_volume (p : SplitPrimes) :
    splitVolume paperModel (uniform paperSupport) 2 1 p=UnramifiedGaugeVolume.splitVolume p := by
  simp only [splitVolume, uniform, IntegralModelWeights.paper_split_weight]
  rfl

theorem inert_volume (p : InertPrimes) :
    inertVolume paperModel (uniform paperSupport) 2 1 p=UnramifiedGaugeVolume.inertVolume p := by
  simp only [inertVolume, uniform, IntegralModelWeights.paper_inert_weight]
  rfl

theorem ramified_volume :
    ramifiedVolume paperModel (uniform paperSupport) 2 1=RamifiedGaugeVolume.normalizedVolume := by
  rw [ramifiedVolume, uniform, IntegralModelWeights.paper_ramified_weight,
    RamifiedHaarNormalization.paper_norm_integral]
  rfl

theorem tau_value : tau paperModel (uniform paperSupport) 2 1=TamagawaProduct.tau := by
  simp only [tau, split_volume, inert_volume, ramified_volume]
  rfl

theorem coefficient_value : coefficient paperLattices paperModel paperSupport (uniform paperSupport) 2 1=
    2*Cubic.Counting.IntegralPointCountData.alpha/9 := by
  rw [coefficient, ToricPicardSpecialization.theta, tau_value,
    ConeIntegral.cone_constant, TamagawaProduct.tau_value]
  norm_num

theorem positive_coefficient : 0 < coefficient paperLattices paperModel paperSupport (uniform paperSupport) 2 1 := by
  rw [coefficient, ToricPicardSpecialization.theta, tau_value, ConeIntegral.cone_constant]
  norm_num
  exact TamagawaProduct.positive

end Cubic.SantensComparison.ToricCountingSpecialization
