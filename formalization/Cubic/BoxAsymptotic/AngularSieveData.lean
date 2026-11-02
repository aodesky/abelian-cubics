import Cubic.BoxAsymptotic.IdealLargeSieve
import Cubic.BoxAsymptotic.AngularMomentData
import Mathlib.Data.Finset.Lattice.Fold

/-! The finite maximum in `lem:angularLargeSieve`. Ideal norms are positive
integers, so the real cutoffs `0 ≤ Z ≤ Y` give precisely the integer cutoffs
`0, …, floor Y`. The underlying ideals and characters are the actual ones. -/

noncomputable section

namespace Cubic.BoxAsymptotic.AngularSieveData

open Cubic.PoissonSummation.CyclotomicIntegerUnits
open Cubic.BoxAsymptotic.IdealAngularData Cubic.BoxAsymptotic.IdealLargeSieve
open Cubic.BoxAsymptotic.AngularMomentData

def residueModes (K : ℝ) (r : ℤ) : Finset ℤ :=
  (positiveModes K).filter (fun k => k % 6 = r)

def partialSum (χ a : Ideal Integers → ℂ) (Y : ℝ) (q : ℕ) : ℂ :=
  ∑ I ∈ initial (idealBall Y) q, a I * χ I

def maximal (χ a : Ideal Integers → ℂ) (Y : ℝ) : ℝ :=
  (((Finset.range (⌊Y⌋₊ + 1)).sup (fun q => ‖partialSum χ a Y q‖₊) : NNReal) : ℝ)

theorem maximal_nonneg (χ a : Ideal Integers → ℂ) (Y : ℝ) : 0 ≤ maximal χ a Y :=
  NNReal.coe_nonneg _

theorem maximal_attained (χ a : Ideal Integers → ℂ) (Y : ℝ) :
    ∃ q : ℕ, q ≤ ⌊Y⌋₊ ∧ maximal χ a Y = ‖partialSum χ a Y q‖ := by
  obtain ⟨q, hq, he⟩ := Finset.exists_mem_eq_sup (Finset.range (⌊Y⌋₊ + 1))
    (⟨0, by simp⟩) (fun q => ‖partialSum χ a Y q‖₊)
  exact ⟨q, by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hq,
    congrArg (fun x : NNReal => (x : ℝ)) he⟩

def conjugate (χ : Ideal Integers → ℂ) : Ideal Integers → ℂ := fun I => star (χ I)

end Cubic.BoxAsymptotic.AngularSieveData
