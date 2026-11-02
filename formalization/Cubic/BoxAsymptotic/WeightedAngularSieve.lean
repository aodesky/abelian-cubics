import Cubic.BoxAsymptotic.WeightedIdealSums

/-! The weighted consequence of the maximal angular sieve. Weights may depend
on the frequency; the coefficient function must be the same for every frequency.
The analytic weight estimates are explicit premises here, not literature inputs.
-/

noncomputable section

namespace Cubic.BoxAsymptotic.WeightedAngularSieve

open Cubic.PoissonSummation.CyclotomicIntegerUnits
open Cubic.BoxAsymptotic.AngularSieveData
open Cubic.BoxAsymptotic.WeightedIdealSums
open MeasureTheory

/-- The initial norm range, with a separate differentiable weight for each
frequency and a uniform bound for its endpoint and total variation. -/
theorem initial_bound {ι : Type*} (S : Finset ι)
    (χ : ι → Ideal Integers → ℂ) (a : Ideal Integers → ℂ)
    (w : ι → ℝ → ℂ) {Y V B : ℝ}
    (hwd : ∀ k ∈ S, ∀ x ∈ Set.Icc 1 Y, DifferentiableAt ℝ (w k) x)
    (hwi : ∀ k ∈ S, IntegrableOn (deriv (w k)) (Set.Icc 1 Y))
    (hw : ∀ k ∈ S, ‖w k Y‖ + ∫ x in Set.Ioc 1 Y, ‖deriv (w k) x‖ ≤ V)
    (hb : (∑ k ∈ S, maximal (χ k) a Y ^ 2) ≤ B) :
    (∑ k ∈ S, ‖initialWeighted (χ k) a Y (w k)‖ ^ 2) ≤ V ^ 2 * B := by
  calc
    _ ≤ ∑ k ∈ S, (V * maximal (χ k) a Y) ^ 2 := by
      apply Finset.sum_le_sum
      intro k hk
      apply pow_le_pow_left₀ (norm_nonneg _)
      calc
        _ ≤ maximal (χ k) a Y *
            (‖w k Y‖ + ∫ x in Set.Ioc 1 Y, ‖deriv (w k) x‖) :=
          WeightedIdealSums.initial_bound (χ k) a (hwd k hk) (hwi k hk)
        _ ≤ maximal (χ k) a Y * V :=
          mul_le_mul_of_nonneg_left (hw k hk) (maximal_nonneg _ _ _)
        _ = _ := mul_comm _ _
    _ = V ^ 2 * ∑ k ∈ S, maximal (χ k) a Y ^ 2 := by
      simp only [mul_pow, Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (sq_nonneg V)

/-- A later norm range. The variation bound includes both endpoints, which
accounts for the two partial sums in Abel summation. -/
theorem interval_bound {ι : Type*} (S : Finset ι)
    (χ : ι → Ideal Integers → ℂ) (a : Ideal Integers → ℂ)
    (w : ι → ℝ → ℂ) {X Y V B : ℝ} (hX : 0 ≤ X) (hXY : X ≤ Y)
    (hwd : ∀ k ∈ S, ∀ x ∈ Set.Icc X Y, DifferentiableAt ℝ (w k) x)
    (hwi : ∀ k ∈ S, IntegrableOn (deriv (w k)) (Set.Icc X Y))
    (hw : ∀ k ∈ S,
      ‖w k Y‖ + ‖w k X‖ + ∫ x in Set.Ioc X Y, ‖deriv (w k) x‖ ≤ V)
    (hb : (∑ k ∈ S, maximal (χ k) a Y ^ 2) ≤ B) :
    (∑ k ∈ S, ‖intervalWeighted (χ k) a X Y (w k)‖ ^ 2) ≤ V ^ 2 * B := by
  calc
    _ ≤ ∑ k ∈ S, (V * maximal (χ k) a Y) ^ 2 := by
      apply Finset.sum_le_sum
      intro k hk
      apply pow_le_pow_left₀ (norm_nonneg _)
      calc
        _ ≤ maximal (χ k) a Y *
            (‖w k Y‖ + ‖w k X‖ + ∫ x in Set.Ioc X Y, ‖deriv (w k) x‖) :=
          WeightedIdealSums.interval_bound (χ k) a hX hXY (hwd k hk) (hwi k hk)
        _ ≤ maximal (χ k) a Y * V :=
          mul_le_mul_of_nonneg_left (hw k hk) (maximal_nonneg _ _ _)
        _ = _ := mul_comm _ _
    _ = V ^ 2 * ∑ k ∈ S, maximal (χ k) a Y ^ 2 := by
      simp only [mul_pow, Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (sq_nonneg V)

end Cubic.BoxAsymptotic.WeightedAngularSieve
