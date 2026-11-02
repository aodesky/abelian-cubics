import Cubic.QuadraticCorrespondence.CorrespondencePolynomials
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.SetTheory.Cardinal.Finite

/-!
# The polynomials and coefficient height in the introductory counting theorems

The count is taken over integer polynomials, with the Galois group of their
image in `ℚ[X]` defined using mathlib's splitting field. Finiteness of the
counted sets, needed wherever `Nat.card` is used, is proved in
`PolynomialCountFiniteness`.
-/

noncomputable section

namespace Cubic.Counting.PolynomialCountData

open Polynomial Cubic.QuadraticCorrespondence.CorrespondencePolynomials

def traceOneCubic (a b : ℤ) : ℤ[X] := X ^ 3 - X ^ 2 + C a * X + C b

/-- The coefficient height in `thm:asymptoticPolynomialCount`. -/
def rootHeight (f : ℤ[X]) : ℝ :=
  max (Real.sqrt |(f.coeff 1 : ℝ)|) (|(f.coeff 0 : ℝ)| ^ (1 / 3 : ℝ))

/-- The paper's `F`: monic trace-one integer cubics with Galois group `C₃`. -/
def cyclicPolynomials : Set ℤ[X] :=
  {f | (∃ a b : ℤ, f = traceOneCubic a b) ∧
    HasCyclicCubicGaloisGroup (f.map (Int.castRingHom ℚ))}

def boundedPolynomials (H : ℝ) : Set ℤ[X] :=
  {f | f ∈ cyclicPolynomials ∧ rootHeight f ≤ H}

def polynomialCount (H : ℝ) : ℕ := Nat.card (boundedPolynomials H)

end Cubic.Counting.PolynomialCountData
