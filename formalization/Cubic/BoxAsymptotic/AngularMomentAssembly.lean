import Cubic.BoxAsymptotic.HeckeAnalyticRealization
import Cubic.BoxAsymptotic.AngularContinuation
import Cubic.BoxAsymptotic.AngularFirstMoment
import CubicTargets.BoxAsymptotic.AngularMoment

/-! The last deductions of `lem:moment`, for the constructed analytic functions.
The primitive second moment is a premise of this helper, supplied by
`PrimitiveHeckeMoment.bound` in the full theorem. It is not a literature input.
-/

noncomputable section

namespace Cubic.BoxAsymptotic.AngularMomentAssembly

open Cubic.BoxAsymptotic.AngularMomentData Cubic.BoxAsymptotic.AngularMomentSums
open Cubic.BoxAsymptotic.HeckeAnalyticRealization
open Cubic.BoxAsymptotic.AngularCorrectionBounds

variable (hHecke : CubicTargets.BoxAsymptotic.PrimitiveHecke.BlackBox)

theorem omitted_second {A : ℕ} {C : ℝ}
    (hsecond : ∀ (K t σ : ℝ), 2 ≤ K → 1 / 2 ≤ σ → σ ≤ 3 / 4 →
      (∑ k ∈ evenModes K, ‖primitiveL hHecke k (σ + t * Complex.I)‖ ^ 2) ≤
        C * momentScale A K t)
    (K t σ : ℝ) (hK : 2 ≤ K) (hσ : 1 / 2 ≤ σ) (hσ' : σ ≤ 3 / 4) :
    (∑ k ∈ evenModes K, ‖heckeL hHecke k (σ + t * Complex.I)‖ ^ 2) ≤
      (4 * C) * momentScale A K t := by
  calc
    _ ≤ ∑ k ∈ evenModes K, 4 * ‖primitiveL hHecke k (σ + t * Complex.I)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro k _
      rw [heckeL, norm_mul, mul_pow]
      have hb := HeckeOmitThree.factor_bound k (σ + t * Complex.I) (by simpa using (by linarith : 0 ≤ σ))
      have hq : ‖HeckeOmitThree.factor k (σ + t * Complex.I)‖ ^ 2 ≤ 4 := by
        nlinarith [norm_nonneg (HeckeOmitThree.factor k (σ + t * Complex.I))]
      exact mul_le_mul_of_nonneg_right hq (sq_nonneg _)
    _ = 4 * ∑ k ∈ evenModes K, ‖primitiveL hHecke k (σ + t * Complex.I)‖ ^ 2 :=
      (Finset.mul_sum ..).symm
    _ ≤ 4 * (C * momentScale A K t) :=
      mul_le_mul_of_nonneg_left (hsecond K t σ hK hσ hσ') (by norm_num)
    _ = _ := by ring

theorem angular_factor {k : ℤ} (hk : Even k) (t η : ℝ) (hη : 0 < η) (hη' : η ≤ 1 / 4) :
    ‖angularF hHecke k ((1 / 2 + η : ℝ) + t * Complex.I)‖ ≤
      (2 * absoluteConstant) * η⁻¹ ^ 4 *
        ‖heckeL hHecke k ((1 / 2 + η : ℝ) + t * Complex.I)‖ *
        ‖heckeL hHecke (3 * k) ((1 / 2 + η : ℝ) + t * Complex.I)‖ := by
  let s : ℂ := (1 / 2 + η : ℝ) + t * Complex.I
  have hlocal := AngularFactorBounds.localFactor_bound k s (by dsimp [s]; simp; linarith)
  have hR := value_eta_bound k t hη hη'
  change ‖angularF hHecke k s‖ ≤ _
  rw [angularF, if_pos hk, norm_mul, norm_mul, norm_mul]
  calc
    _ ≤ 2 * ((‖heckeL hHecke k s‖ * ‖heckeL hHecke (3 * k) s‖) *
        (absoluteConstant * η⁻¹ ^ 4)) :=
      mul_le_mul hlocal
        (mul_le_mul_of_nonneg_left hR (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
        (by positivity) (by norm_num)
    _ = _ := by dsimp [s]; ring

/-- Assembly from the second moment for the actual primitive functions. The
full theorem supplies this estimate by the weighted AFE and angular sieve. -/
theorem of_primitive_second
    {A : ℕ} {C : ℝ} (hC : 0 < C)
    (hsecond : ∀ (K t σ : ℝ), 2 ≤ K → 1 / 2 ≤ σ → σ ≤ 3 / 4 →
      (∑ k ∈ evenModes K, ‖primitiveL hHecke k (σ + t * Complex.I)‖ ^ 2) ≤
        C * momentScale A K t) :
    CubicTargets.BoxAsymptotic.AngularMomentClaim := by
  let C₂ := 4 * C
  let Cᵣ := 2 * absoluteConstant
  let C₁ := 2 * (Cᵣ * C₂ * (1 + 3 ^ (A + 1)))
  have hC₂ : 0 < C₂ := by dsimp [C₂]; positivity
  have hCᵣ : 0 < Cᵣ := mul_pos (by norm_num) absoluteConstant_pos
  have hC₁ : 0 < C₁ := by dsimp [C₁]; positivity
  have hreal := realization hHecke
  have htwo := omitted_second hHecke hsecond
  have hpositive := AngularFirstMoment.positive_bound
    (heckeL hHecke) (angularF hHecke) A C₂ Cᵣ hC₂.le hCᵣ.le htwo
    (fun k t η _ hk hη hη' => angular_factor hHecke hk t η hη hη')
    (fun k _ _ hk _ => if_neg hk)
  have hconj (k : ℤ) (t η : ℝ) (hk : 0 < k) (hη : 0 < η) :
      angularF hHecke (-k) ((1 / 2 + η : ℝ) + t * Complex.I) =
        star (angularF hHecke k ((1 / 2 + η : ℝ) + (-t) * Complex.I)) := by
    have hs : (1 / 2 : ℝ) < (((1 / 2 + η : ℝ) : ℂ) + t * Complex.I).re := by simp; linarith
    simpa using AngularContinuation.neg_index hreal (ne_of_gt hk) hs
  have hfirst := AngularFirstMoment.signed_bound (angularF hHecke) A
    (Cᵣ * C₂ * (1 + 3 ^ (A + 1))) hpositive hconj
  refine ⟨heckeL hHecke, angularF hHecke, hreal, A, C₂ + C₁, add_pos hC₂ hC₁, ?_, ?_⟩
  · intro K t σ hK hσ hσ'
    exact (htwo K t σ hK hσ hσ').trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hC₁.le) (scale_nonneg A hK t))
  · intro K t η hK hη hη'
    exact (hfirst K t η hK hη hη').trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC₂.le) (by positivity))
        (scale_nonneg A hK t))

end Cubic.BoxAsymptotic.AngularMomentAssembly
