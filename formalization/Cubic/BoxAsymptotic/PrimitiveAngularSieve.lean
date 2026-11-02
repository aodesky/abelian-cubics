import Cubic.BoxAsymptotic.AngularLargeSieve

/-! The maximal estimate for the primitive characters used in the AFE.
The proved sieve for all chosen generator phases controls both the full ideal
sum and the sum omitting three. Splitting according to whether six divides
the frequency costs only an absolute factor two. -/

noncomputable section

namespace Cubic.BoxAsymptotic.PrimitiveAngularSieve

open Cubic.PoissonSummation.CyclotomicIntegerUnits
open Cubic.BoxAsymptotic.AngularIdealData Cubic.BoxAsymptotic.IdealAngularData
open Cubic.BoxAsymptotic.AngularSieveData Cubic.BoxAsymptotic.AngularMomentData
open Cubic.BoxAsymptotic.AngularMaximalSums
open CubicTargets.BoxAsymptotic

theorem bound (hLS : AdditiveLargeSieve.BlackBox) (hRM : BinaryDecomposition.BlackBox) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K Y : ℝ), 2 ≤ K → 2 ≤ Y →
      ∀ (a : Ideal Integers → ℂ),
        (∀ I ∈ idealBall Y, ‖a I‖ ≤ 1 / Real.sqrt (Ideal.absNorm I)) →
        ((∑ k ∈ evenModes K, maximal (primitivePsi k) a Y ^ 2) ≤
          C * (K + Y) * Real.log (2 * Y) ^ 5) ∧
        ((∑ k ∈ evenModes K, maximal (conjugate (primitivePsi k)) a Y ^ 2) ≤
          C * (K + Y) * Real.log (2 * Y) ^ 5) := by
  obtain ⟨C, hC, hb⟩ := generator_bound hLS hRM
  refine ⟨2 * C, mul_pos (by norm_num) hC, fun K Y hK hY a ha => ?_⟩
  have hp (b : Ideal Integers → ℂ)
      (hb' : ∀ I ∈ idealBall Y, ‖b I‖ ≤ 1 / Real.sqrt (Ideal.absNorm I)) :
      (∑ k ∈ evenModes K, maximal (primitivePsi k) b Y ^ 2) ≤
        (2 * C) * (K + Y) * Real.log (2 * Y) ^ 5 := by
    have hfull := hb K Y hK hY b hb'
    have haway := hb K Y hK hY (away b)
      (fun I hI => (norm_away_le b I).trans (hb' I hI))
    calc
      _ ≤ ∑ k ∈ evenModes K,
          (maximal (generatorPhase k) b Y ^ 2 + maximal (generatorPhase k) (away b) Y ^ 2) := by
        apply Finset.sum_le_sum
        intro k _
        by_cases hk : 6 ∣ k
        · have he : primitivePsi k = generatorPhase k := funext (fun I => if_pos hk)
          rw [he]
          exact le_add_of_nonneg_right (sq_nonneg _)
        · have he : primitivePsi k = psi k := funext (fun I => if_neg hk)
          rw [he, maximal_away]
          exact le_add_of_nonneg_left (sq_nonneg _)
      _ ≤ ∑ k ∈ positiveModes K,
          (maximal (generatorPhase k) b Y ^ 2 + maximal (generatorPhase k) (away b) Y ^ 2) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => add_nonneg (sq_nonneg _) (sq_nonneg _))
      _ ≤ _ := by rw [Finset.sum_add_distrib]; linarith
  refine ⟨hp a ha, ?_⟩
  simpa only [maximal_conjugate] using hp (conjugate a)
    (fun I hI => by simpa only [conjugate, norm_star] using ha I hI)

end Cubic.BoxAsymptotic.PrimitiveAngularSieve
