import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

namespace Cubic.Introduction.CubeIdealSumData

/-- Genuine ideal counts; the unused zeroth Dirichlet coefficient is set to zero. -/
def coefficient (K : Type) [Field K] [NumberField K] (n : ℕ) : ℂ :=
  if n = 0 then 0 else
    Nat.card {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = n ^ 3}

def summatory (K : Type) [Field K] [NumberField K] (X : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, coefficient K n

def error (X : ℝ) : ℝ := Real.sqrt X * Real.log X ^ 3 * Real.log (Real.log X) ^ 2

def heightError (H : ℝ) : ℝ := H * Real.log H ^ 3 * Real.log (Real.log H) ^ 2

end Cubic.Introduction.CubeIdealSumData
