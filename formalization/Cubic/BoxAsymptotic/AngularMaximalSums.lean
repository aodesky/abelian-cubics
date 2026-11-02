import Cubic.BoxAsymptotic.AngularSieveFrequencies
import Cubic.BoxAsymptotic.AngularSieveData

/-! Maxima, conjugate characters and omission of the factor at three. -/

noncomputable section

namespace Cubic.BoxAsymptotic.AngularMaximalSums

open Cubic.PoissonSummation.CyclotomicIntegerUnits
open Cubic.BoxAsymptotic.AngularIdealData Cubic.BoxAsymptotic.IdealAngularData
open Cubic.BoxAsymptotic.AngularSieveData Cubic.BoxAsymptotic.AngularMomentData
open Cubic.BoxAsymptotic.IdealLargeSieve
open CubicTargets.BoxAsymptotic

theorem partial_le_maximal (χ a : Ideal Integers → ℂ) (Y : ℝ) {q : ℕ}
    (hq : q ≤ ⌊Y⌋₊) : ‖partialSum χ a Y q‖ ≤ maximal χ a Y := by
  exact_mod_cast Finset.le_sup (f := fun q => ‖partialSum χ a Y q‖₊)
    (show q ∈ Finset.range (⌊Y⌋₊ + 1) from Finset.mem_range.mpr (by omega))

theorem partial_floor (χ a : Ideal Integers → ℂ) (Y : ℝ) {Z : ℝ} (hZ : 0 ≤ Z) :
    (∑ I ∈ (idealBall Y).filter (fun I => (Ideal.absNorm I : ℝ) ≤ Z), a I * χ I) =
      partialSum χ a Y ⌊Z⌋₊ := by
  classical
  unfold partialSum initial
  congr 1
  ext I
  simp only [Finset.mem_filter, Nat.le_floor_iff hZ]

theorem maximal_conjugate (χ a : Ideal Integers → ℂ) (Y : ℝ) :
    maximal (conjugate χ) a Y = maximal χ (conjugate a) Y := by
  have he (q : ℕ) : partialSum (conjugate χ) a Y q =
      star (partialSum χ (conjugate a) Y q) := by
    simp [partialSum, conjugate]
  unfold maximal
  congr 1
  apply Finset.sup_congr rfl
  intro q hq
  simp only [he, nnnorm_star]

def away (a : Ideal Integers → ℂ) (I : Ideal Integers) : ℂ :=
  if 3 ∣ Ideal.absNorm I then 0 else a I

theorem norm_away_le (a : Ideal Integers → ℂ) (I : Ideal Integers) :
    ‖away a I‖ ≤ ‖a I‖ := by
  unfold away
  split_ifs <;> simp

theorem partial_away (k : ℤ) (a : Ideal Integers → ℂ) (Y : ℝ) (q : ℕ) :
    partialSum (psi k) a Y q = partialSum (generatorPhase k) (away a) Y q := by
  apply Finset.sum_congr rfl
  intro I hI
  by_cases h : 3 ∣ Ideal.absNorm I
  · simp [psi, away, h]
  · rw [away, if_neg h, generatorPhase_away k h]

theorem maximal_away (k : ℤ) (a : Ideal Integers → ℂ) (Y : ℝ) :
    maximal (psi k) a Y = maximal (generatorPhase k) (away a) Y := by
  unfold maximal
  simp_rw [partial_away]

theorem generator_bound
    (hLS : AdditiveLargeSieve.BlackBox) (hRM : BinaryDecomposition.BlackBox) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K Y : ℝ), 2 ≤ K → 2 ≤ Y →
      ∀ (a : Ideal Integers → ℂ),
        (∀ I ∈ idealBall Y, ‖a I‖ ≤ 1 / Real.sqrt (Ideal.absNorm I)) →
      (∑ k ∈ positiveModes K, maximal (generatorPhase k) a Y ^ 2) ≤
        C * (K + Y) * Real.log (2 * Y) ^ 5 := by
  obtain ⟨C, hC, hb⟩ := AngularSieveFrequencies.dyadic_bound hLS hRM
  refine ⟨C, hC, fun K Y hK hY a ha => ?_⟩
  choose q hq he using (fun k => maximal_attained (generatorPhase k) a Y)
  have h := hb K Y hK hY (idealBall Y) (Finset.Subset.refl _) a ha q hq
  simpa only [he, partialSum] using h

end Cubic.BoxAsymptotic.AngularMaximalSums
