import Cubic.Counting.PolynomialCountData
import Cubic.Counting.AsymptoticConstantsData
import Cubic.PoissonSummation.HeightCountingData

/-!
# Objects in the count of all monic abelian cubics

`F_mon` is the set of monic integral cubics `t³ + a₂t² + a₁t + a₀` whose image in `ℚ[t]` has
Galois group `C₃`, and `H_w(f) = max(|a₂|, |a₁|^{1/2}, |a₀|^{1/3})`. For such `f`, the
trace is `s = -a₂` and the translation-invariant quantity is `n = a₂² - 3a₁`.

`A₁(X)` counts the trace-one polynomials `t³ - t² + at + b ∈ F` with `1 - 3a ≤ X`, and
`A₀(X)` counts the trace-zero polynomials `t³ - Nt + c` with Galois group `C₃` and
`1 ≤ N ≤ X`. `r(N)` is the number of `c ∈ ℤ` for which `4N³ - 27c²` is a square.

`C` and `D` are the constants of the trace-one count (`thm:asymptoticPolynomialCount`):
`C = originalLeading` and `D = C · originalSecondaryRatio`.
-/

noncomputable section

namespace Cubic.Counting.GeneralMonicData

open Polynomial Cubic.Counting.PolynomialCountData
open Cubic.QuadraticCorrespondence.CorrespondencePolynomials

/-- The monic cubic `t³ + a₂t² + a₁t + a₀`. -/
def monicCubic (a₂ a₁ a₀ : ℤ) : ℤ[X] := X ^ 3 + C a₂ * X ^ 2 + C a₁ * X + C a₀

/-- `F_mon`: monic integral cubics with Galois group `C₃`. -/
def monicCyclic : Set ℤ[X] :=
  {f | (∃ a₂ a₁ a₀ : ℤ, f = monicCubic a₂ a₁ a₀) ∧
    HasCyclicCubicGaloisGroup (f.map (Int.castRingHom ℚ))}

/-- The weighted coefficient height `H_w(f) = max(|a₂|, |a₁|^{1/2}, |a₀|^{1/3})`. -/
def weightedHeight (f : ℤ[X]) : ℝ :=
  max |(f.coeff 2 : ℝ)| (max (Real.sqrt |(f.coeff 1 : ℝ)|) (|(f.coeff 0 : ℝ)| ^ (1 / 3 : ℝ)))

/-- The polynomials in `F_mon` of weighted height at most `H`. -/
def generalSet (H : ℝ) : Set ℤ[X] := {f | f ∈ monicCyclic ∧ weightedHeight f ≤ H}

/-- The trace `s = -a₂`. -/
def trace (f : ℤ[X]) : ℤ := -f.coeff 2

/-- The invariant `n = a₂² - 3a₁`. -/
def invariant (f : ℤ[X]) : ℤ := f.coeff 2 ^ 2 - 3 * f.coeff 1

/-- Trace-one polynomials in `F` with `1 - 3a ≤ X`. -/
def traceOneSet (X : ℝ) : Set ℤ[X] :=
  {f | f ∈ cyclicPolynomials ∧ ((1 - 3 * f.coeff 1 : ℤ) : ℝ) ≤ X}

/-- `A₁(X)`. -/
def A₁ (X : ℝ) : ℕ := Nat.card (traceOneSet X)

/-- Trace-zero polynomials `t³ - Nt + c` with Galois group `C₃` and `1 ≤ N ≤ X`. -/
def traceZeroSet (X : ℝ) : Set ℤ[X] :=
  {f | ∃ N c : ℤ, f = monicCubic 0 (-N) c ∧ 1 ≤ N ∧ (N : ℝ) ≤ X ∧
    HasCyclicCubicGaloisGroup (f.map (Int.castRingHom ℚ))}

/-- `A₀(X)`. -/
def A₀ (X : ℝ) : ℕ := Nat.card (traceZeroSet X)

/-- The `c ∈ ℤ` for which `4N³ - 27c²` is a square. -/
def squareSet (N : ℤ) : Set ℤ := {c | IsSquare (4 * N ^ 3 - 27 * c ^ 2)}

/-- `r(N)`. -/
def r (N : ℤ) : ℕ := Nat.card (squareSet N)

/-- The Dirichlet coefficients `d_n` of `Z₀(s)`. -/
def d (n : ℕ) : ℕ := Cubic.PoissonSummation.HeightCountingData.count n

/-- The constant `C` of the trace-one count. -/
def Cconst : ℝ := AsymptoticConstantsData.originalLeading

/-- The constant `D` of the trace-one count. -/
def Dconst : ℝ := AsymptoticConstantsData.originalLeading * AsymptoticConstantsData.originalSecondaryRatio

end Cubic.Counting.GeneralMonicData
