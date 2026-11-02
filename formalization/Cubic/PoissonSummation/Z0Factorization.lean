import Cubic.PoissonSummation.EulerCorrectionFactor
import Cubic.PoissonSummation.SimplifiedHeightZeta
import CubicTargets.PoissonSummation.Z0Factorization

noncomputable section

namespace Cubic.PoissonSummation.Z0Factorization

theorem «eqn:Z0factorization»
    (hPoisson : CubicTargets.PoissonSummation.PoissonWithDualMeasure.BlackBox) :
    CubicTargets.PoissonSummation.Z0Factorization.Claim := by
  intro z hz
  have h := («lemma:simplifiedZ(s)» hPoisson).formula (2 * z) 0 (by
    simp only [mul_zero, add_zero, Complex.mul_re]
    norm_num
    linarith)
  have hp : HeightZetaFormulaData.parameter (2 * z) 0 = z := by
    unfold HeightZetaFormulaData.parameter
    ring
  rw [hp] at h
  change AdelicHeightZetaData.heightZeta (2 * z) 0 = _
  rw [h]
  unfold CubicTargets.PoissonSummation.SimplifiedHeightZeta.simplified EulerCorrectionData.R
  ring

end Cubic.PoissonSummation.Z0Factorization
