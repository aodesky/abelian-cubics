import Cubic.BoxAsymptotic.AngularLargeSieve

/-! Exact-label projection `eq:angularMaximal` of the full angular sieve lemma.
This equation is a supporting result, not an additional paper milestone. -/

namespace Cubic.BoxAsymptotic.AngularMaximal

open Cubic.PoissonSummation.CyclotomicIntegerUnits
open Cubic.BoxAsymptotic.AngularIdealData Cubic.BoxAsymptotic.IdealAngularData
open Cubic.BoxAsymptotic.AngularSieveData
open CubicTargets.BoxAsymptotic

theorem «eq:angularMaximal»
    (hLS : AdditiveLargeSieve.BlackBox) (hRM : BinaryDecomposition.BlackBox) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K Y : ℝ), 2 ≤ K → 2 ≤ Y →
      ∀ (r : ℤ), r ∈ ({0, 2, 4} : Finset ℤ) →
      ∀ (a : Ideal Integers → ℂ),
        (∀ I ∈ idealBall Y, ‖a I‖ ≤ 1 / Real.sqrt (Ideal.absNorm I)) →
        (∑ k ∈ residueModes K r, maximal (psi k) a Y ^ 2) ≤
          C * (K + Y) * Real.log (2 * Y) ^ 5 := by
  obtain ⟨C, hC, h⟩ := AngularLargeSieve.«lem:angularLargeSieve» hLS hRM
  exact ⟨C, hC, fun K Y hK hY r hr a ha => (h K Y hK hY r hr a ha).1⟩

end Cubic.BoxAsymptotic.AngularMaximal
