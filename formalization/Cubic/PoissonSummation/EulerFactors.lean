import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Algebra of the local Euler factors

Supporting identities for `lemma:simplifiedZ(s)` and `prop:leadingTerms`.
Here `x` represents `p⁻ᶻ`. These are finite algebraic identities; convergence,
infinite products, meromorphic continuation and differentiation are established where the corresponding paper result is assembled.
-/

namespace Cubic.PoissonSummation

/-- The split-prime correction factor in the paper's height zeta function. -/
def splitCorrection {R : Type*} [CommRing R] (x : R) : R :=
  1 - 3 * x ^ 2 + 2 * x ^ 3

/-- Polynomial factorization underlying `lemma:simplifiedZ(s)`. -/
theorem splitCorrection_factor {R : Type*} [CommRing R] (x : R) :
    splitCorrection x = (1 - x) ^ 2 * (1 + 2 * x) := by
  unfold splitCorrection
  ring

/-- The local identity from the former longer proof of `lemma:simplifiedZ(s)`.
The nonvanishing hypothesis is essential in a field with totalized division. -/
theorem split_euler_cancellation {K : Type*} [Field K] (x : K) (hx : 1 - x ≠ 0) :
    (1 + 3 * x / (1 - x)) * (1 - x) ^ 3 = splitCorrection x := by
  unfold splitCorrection
  field_simp
  ring

/-- The inert Euler factor after multiplying by the Riemann-zeta factor. -/
theorem inert_euler_combination {K : Type*} [Field K] (x : K) :
    (1 - x)⁻¹ * (1 + x)⁻¹ = (1 - x ^ 2)⁻¹ := by
  rw [← mul_inv]
  congr 1
  ring

/-- The quotient of correction factors used in `prop:leadingTerms`. -/
theorem splitCorrection_div_inert {K : Type*} [Field K] (x : K)
    (hminus : 1 - x ≠ 0) (hplus : 1 + x ≠ 0) :
    splitCorrection x / (1 - x ^ 2) = (1 - x) * (1 + 2 * x) / (1 + x) := by
  have hfactor : 1 - x ^ 2 = (1 - x) * (1 + x) := by ring
  rw [splitCorrection_factor, hfactor]
  field_simp

/-- The simplified split factor, still with `x = p⁻ᶻ`. -/
theorem splitCorrection_quotient {K : Type*} [Field K] (x : K)
    (hminus : 1 - x ≠ 0) (hplus : 1 + x ≠ 0) :
    splitCorrection x / (1 - x ^ 2) = 1 - 2 * x ^ 2 / (1 + x) := by
  rw [splitCorrection_div_inert x hminus hplus]
  field_simp
  ring

/-- The form displayed in the paper, where `y = pᶻ`. -/
theorem splitCorrection_reciprocal {K : Type*} [Field K] (y : K)
    (hy : y ≠ 0) (hminus : 1 - y⁻¹ ≠ 0) (hplus : 1 + y⁻¹ ≠ 0)
    (hyplus : y + 1 ≠ 0) :
    splitCorrection y⁻¹ / (1 - (y⁻¹) ^ 2) = 1 - 2 / (y * (y + 1)) := by
  rw [splitCorrection_quotient y⁻¹ hminus hplus]
  field_simp

end Cubic.PoissonSummation
