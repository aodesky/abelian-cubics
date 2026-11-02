import Cubic.Counting.HeightCoefficientData
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Cited black box: [Topacogullari 2021, Theorem 1.5]

B. Topacogullari, *The fourth moment of individual Dirichlet L-functions on the critical
line*, Math. Z. 298 (2021) 577–624, arXiv:1909.11517, Theorem 1.5:

> Let `ε > 0`. Let `K` be a quadratic number field with discriminant `D`. Then we have,
> for `T ≥ 1`,
> `∫_1^T |ζ_K(1/2 + it)|² dt = ∫_1^T P_K(log t) dt + O(|D|^{2/3} T^{2/3+ε} + |D|^{5/4 − 3θ/2} T^{1/2+θ+ε})`,
> where `P_K` is a quadratic polynomial, whose coefficients depend only on the field `K`,
> and where the implicit constant depends only on `ε`.

This is the statement specialized to `K = ℚ(√-3)`, `D = -3`, with nothing added:

* `ζ_K = ζ · L(·, χ_D)`, as Topacogullari writes just before the theorem. `χ_{-3}` is
  `QuadraticDirichletCharacter.character` (values `1, -1, 0` on the classes `1, 2, 0`
  mod 3). `zetaE` uses mathlib's continuations of both factors.
* `θ = 7/64`, the value Topacogullari states is admissible (§3.1, by Kim–Sarnak).
  The theorem is stated for this fixed value because the general notion of an
  admissible `θ` (a bound towards Ramanujan–Petersson for exceptional spectral
  parameters) cannot be stated without Maass forms.
* For a fixed field, "the implicit constant depends only on `ε`" becomes `∃ C` after
  `∀ ε`, and "`P_K` depends only on `K`" puts `∃ P` before `∀ ε`.
* "Quadratic polynomial" is `P.natDegree = 2`, with real coefficients (the integrand
  `P_K(log t)` is real).

It is a proposition definition: it has no proof and introduces no axiom. Proofs using it
carry it as a visible hypothesis.
-/

noncomputable section

namespace CubicTargets.Counting.TopacogullariSecondMoment

open Cubic.Counting.HeightCoefficientData

/-- [Topacogullari 2021, Theorem 1.5] for `K = ℚ(√-3)`, with `θ = 7/64`. -/
def BlackBox : Prop :=
  ∃ P : Polynomial ℝ, P.natDegree = 2 ∧
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ T : ℝ, 1 ≤ T →
      |(∫ t in (1 : ℝ)..T, ‖zetaE ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2) -
          ∫ t in (1 : ℝ)..T, P.eval (Real.log t)| ≤
        C * ((3 : ℝ) ^ (2 / 3 : ℝ) * T ^ (2 / 3 + ε) +
          (3 : ℝ) ^ (5 / 4 - 3 / 2 * (7 / 64) : ℝ) * T ^ (1 / 2 + 7 / 64 + ε))

end CubicTargets.Counting.TopacogullariSecondMoment
