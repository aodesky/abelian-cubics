import CubicTargets.Counting.NormalityCriterion
import Cubic.Counting.NormalityTracePairing
import Cubic.Counting.CubicTraceCoefficients

/-!
# The normality criterion via the rational trace pairing

Normality is equivalent to nonsingularity of the trace Gram matrix. Its
determinant is the square of Section 2's group-algebra multiplication
determinant, namely `e₁(e₁² - 3e₂)`. All computations take place over `ℚ`
and in the actual cubic algebra, including the split case.
-/

noncomputable section

namespace Cubic.Counting.NormalityCriterion
open Polynomial Cubic.OrbitParametrization Cubic.OrbitParametrization.C3Algebra
open NormalityTracePairing

/-- The first two elementary symmetric functions of the conjugates are the
coefficients of the actual multiplication characteristic polynomial.
The usual trace identities verify this directly on a rational basis. -/
theorem coefficients (K : C3Alg) (x : K.carrier) (e₁ e₂ e₃ : ℚ)
    (hc : (LinearMap.mul ℚ K.carrier x).charpoly =
      X ^ 3 - C e₁ * X ^ 2 + C e₂ * X - C e₃) :
    x + K.act σ x + K.act (σ ^ 2) x = algebraMap ℚ K.carrier e₁ ∧
    secondCoeff x (K.act σ x) (K.act (σ ^ 2) x) = algebraMap ℚ K.carrier e₂ := by
  let b := Module.finBasisOfFinrankEq ℚ K.carrier (finrank_eq_three K)
  obtain ⟨ht, ht2⟩ := CubicTraceCoefficients.traces b x e₁ e₂ e₃ hc
  have hs : x + K.act σ x + K.act (σ ^ 2) x = algebraMap ℚ K.carrier e₁ := by
    rw [← traceSum_eq, ← algebraMap_trace, ht]
  refine ⟨hs, ?_⟩
  have hs2 : x ^ 2 + (K.act σ x) ^ 2 + (K.act (σ ^ 2) x) ^ 2 =
      (algebraMap ℚ K.carrier e₁) ^ 2 - 2 * algebraMap ℚ K.carrier e₂ := by
    have h := congrArg (algebraMap ℚ K.carrier) ht2
    simpa only [algebraMap_trace, traceSum_eq, map_pow, map_sub, map_mul, map_ofNat] using h
  have htwo : IsUnit (2 : K.carrier) := by
    simpa only [map_ofNat] using
      (isUnit_iff_ne_zero.mpr (by norm_num : (2 : ℚ) ≠ 0)).map (algebraMap ℚ K.carrier)
  apply htwo.mul_left_cancel
  dsimp [secondCoeff]
  linear_combination (congrArg (fun y : K.carrier => y ^ 2) hs) - hs2

/-- The determinant of the rational trace Gram matrix, as computed in the paper. -/
theorem gram_det_eq (K : C3Alg) (x : K.carrier) (e₁ e₂ e₃ : ℚ)
    (hc : (LinearMap.mul ℚ K.carrier x).charpoly =
      X ^ 3 - C e₁ * X ^ 2 + C e₂ * X - C e₃) :
    (gram K x).det = (e₁ * (e₁ ^ 2 - 3 * e₂)) ^ 2 := by
  apply (algebraMap ℚ K.carrier).injective
  rw [gram_det, Cubic.Counting.«eqn:normalityDeterminant»]
  obtain ⟨h1, h2⟩ := coefficients K x e₁ e₂ e₃ hc
  rw [h1, h2]
  simp only [map_pow, map_mul, map_sub, map_ofNat]

theorem «lemma:normalityCriterion» : CubicTargets.Counting.NormalityCriterion.Claim := by
  intro K x e₁ e₂ e₃ hc
  rw [normal_iff_gram_det_ne_zero, gram_det_eq K x e₁ e₂ e₃ hc]
  exact pow_ne_zero_iff (by norm_num)

end Cubic.Counting.NormalityCriterion
