import Cubic.PoissonSummation.LeadingTermsAssembly
import Cubic.PoissonSummation.EulerCorrectionFactor

/-! The current manuscript's Laurent expansion and derivative ratio in `z=s/2`.
These are consequences of the same actual height-series expansion, with every
chain factor proved rather than merely described in correspondence notes. -/

noncomputable section

namespace Cubic.PoissonSummation.LeadingTermsNormalization

open Filter Asymptotics CubicTargets.PoissonSummation.LeadingTerms
open scoped Topology

variable {D F : ℂ → ℂ} {μ c₂ c₁ : ℂ} (h : Expansion D F μ c₂ c₁)

include h

theorem laurent_z :
    (fun z : ℂ => F (2 * z) - c₂ / (4 * (z - 1) ^ 2) - c₁ / (2 * (z - 1)))
      =O[𝓝[≠] (1 : ℂ)] (fun _ => (1 : ℂ)) := by
  have ht : Tendsto (fun z : ℂ => 2 * z) (𝓝[≠] (1 : ℂ)) (𝓝[≠] (2 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using ((continuous_const.mul continuous_id).tendsto (1 : ℂ)).mono_left
        (nhdsWithin_le_nhds : 𝓝[≠] (1 : ℂ) ≤ 𝓝 1)
    · filter_upwards [self_mem_nhdsWithin] with z hz
      change 2 * z ≠ 2
      intro he
      apply hz
      change z = 1
      linear_combination he / 2
  have ho := h.laurent.comp_tendsto ht
  convert ho using 1
  ext z
  dsimp only [Function.comp_apply]
  have he : 2 * z - 2 = 2 * (z - 1) := by ring
  simp only [he, mul_pow]
  norm_num

theorem leading_z : c₂ = 4 *
    DirichletCharacter.LFunction QuadraticDirichletCharacter.character 1 ^ 2 *
      EulerCorrectionData.E 1 := by
  simpa only [EulerCorrectionFactor.correction_rescaling, mul_one] using h.leading

theorem subleading_z : c₁ / c₂ = μ +
    deriv EulerCorrectionData.E 1 / (2 * EulerCorrectionData.E 1) := by
  rw [EulerCorrectionFactor.derivative_rescaling 1 (by norm_num),
    EulerCorrectionFactor.correction_rescaling]
  simpa only [mul_one, mul_div_mul_left _ _ (by norm_num : (2 : ℂ) ≠ 0)] using h.subleading

end Cubic.PoissonSummation.LeadingTermsNormalization
