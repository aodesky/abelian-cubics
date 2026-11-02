import CubicTargets.Counting.XiMeanValue
import Cubic.Counting.XiMeanBound

namespace Cubic.Counting.XiMeanValue

theorem «lemma:xiMeanValue»
    (hCN : CubicTargets.Counting.ChandrasekharanNarasimhanMeanSquare.BlackBox) :
    CubicTargets.Counting.XiMeanValue.Claim :=
  XiMeanBound.«eqn:xiMeanBound» hCN

/-- Restriction to an inner strip, retained for the direct summatory argument. -/
theorem inner_strip
    (hCN : CubicTargets.Counting.ChandrasekharanNarasimhanMeanSquare.BlackBox)
    (δ : ℝ) (hδ : 0 < δ) (η : ℝ) (hη : 0 < η) :
    ∃ K : ℝ, ∀ σ : ℝ, 1 / 2 + δ ≤ σ → σ ≤ 2 → ∀ U : ℝ, 2 ≤ U →
      (∫ t in U..2 * U, ‖Cubic.Counting.HeightCoefficientData.zetaE
        ((σ : ℂ) + t * Complex.I)‖ ^ 2) ≤ K * U ^ (1 + η) := by
  obtain ⟨K, hK⟩ := «lemma:xiMeanValue» hCN η hη
  exact ⟨K, fun σ hσ hσ2 U hU => hK σ (by linarith) hσ2 U hU⟩

end Cubic.Counting.XiMeanValue
