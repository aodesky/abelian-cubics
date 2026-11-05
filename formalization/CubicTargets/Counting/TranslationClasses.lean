import Cubic.Counting.TranslationClassData
import CubicTargets.Counting.GeneralMonic

/-!
# Target for `rem:translationClasses`

The remark derives the count, stated in the introduction's comparison with Xiao, of
translation classes of monic integral `C₃` cubics ordered by the Bhargava–Shankar height
`H_BS(f) = max(|I|³, J²/4)`:
`#{f : H_BS(f) ≤ H} = H^{1/3} P_BS(log H) + O_ε(H^{1/6+ε})`.

The claim records every assertion of the remark: `I = n(f)`; each class has exactly one
representative of trace `-1`, `0` or `1`; `C(Y) = 2A₁(Y) + A₀(Y/3)` with finiteness; the
asymptotic for `C(Y)`; `4I³ - J² = 27 disc(f) > 0` and `H_BS(f) = I³`; and the final
estimate with the displayed polynomial `P_BS`. Translation classes are the quotient of
`F_mon` by `f(t) ~ f(t + k)`, `k ∈ ℤ` (`Cubic.Counting.TranslationClassData`). The
Euler–Kronecker constant `μ` is characterized as in `GeneralMonicCountClaim`.
-/

noncomputable section

namespace CubicTargets.Counting.TranslationClasses

open Filter Asymptotics
open Cubic.Counting.GeneralMonicData Cubic.Counting.TranslationClassData
open Cubic.Counting.IntegralPointCountData
open CubicTargets.Counting.GeneralMonic (HasMainTerm)
open CubicTargets.Counting.AsymptoticPolynomialCount (EulerKronecker)

/-- `P_BS(X) = (11α/162)(X + 6μ - 6ζ'(2)/ζ(2) + 6β - 3 - (15/44) log 3) - π/(3√3)`. -/
def PBS (μ : ℂ) (X : ℝ) : ℝ :=
  11 * alpha / 162 * (X + 6 * μ.re - 6 * (deriv riemannZeta 2 / riemannZeta 2).re +
    6 * beta - 3 - 15 / 44 * Real.log 3) - Real.pi / (3 * Real.sqrt 3)

/-- `rem:translationClasses`, ending with the introduction's estimate for `H_BS`. -/
def Claim : Prop :=
  ∃ (Z : ℂ → ℂ) (μ : ℂ), EulerKronecker Z μ ∧
    -- `I = n(f)`; `4I³ - J² = 27 disc(f) > 0`, so `H_BS(f) = I³`
    (∀ f ∈ monicCyclic, bsI f = invariant f ∧ 0 < bsI f ∧
      4 * bsI f ^ 3 - bsJ f ^ 2 = 27 * discriminant f ∧ 0 < discriminant f ∧
      bsHeight f = (bsI f : ℝ) ^ 3) ∧
    -- exactly one representative of trace `-1`, `0` or `1` in each class
    (∀ c : TranslationClass, ∃! f : monicCyclic,
      TranslationClass.mk f = c ∧ trace f ∈ ({-1, 0, 1} : Set ℤ)) ∧
    -- `C(Y) = 2A₁(Y) + A₀(Y/3)`
    (∀ Y : ℝ, (classesUpTo Y).Finite ∧ classCount Y = 2 * A₁ Y + A₀ (Y / 3)) ∧
    -- `C(Y) = Y((11/6)Q(½ log Y) - (19α/108) log 3 - π/(3√3)) + O_ε(Y^{1/2+ε})`
    HasMainTerm (fun Y => (classCount Y : ℝ))
      (fun Y => Y * (11 / 6 * Q μ (1 / 2 * Real.log Y) - 19 * alpha / 108 * Real.log 3 -
        Real.pi / (3 * Real.sqrt 3))) ∧
    -- `#{f : H_BS(f) ≤ H} = H^{1/3} P_BS(log H) + O_ε(H^{1/6+ε})`
    (∀ H : ℝ, (bsClasses H).Finite) ∧
    ∀ ε : ℝ, 0 < ε →
      (fun H : ℝ => (bsCount H : ℝ) - H ^ (1 / 3 : ℝ) * PBS μ (Real.log H))
        =O[atTop] (fun H : ℝ => H ^ (1 / 6 + ε))

end CubicTargets.Counting.TranslationClasses
