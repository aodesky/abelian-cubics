import CubicTargets.Counting.CubicImpliesNormalTarget
import Cubic.Counting.PolynomialCountData
import Cubic.OrbitParametrization.TraceOne

/-!
# `cor:automaticallyNormal`

"Let `𝓕` denote the set of polynomials of the form `t³−t²+at+b ∈ ℤ[t]` which either
have Galois group `C₃` or split into three linear factors over `ℚ`. Then any `f ∈ 𝓕`
is normal."

* `𝓕` is `family`: `f = traceOneCubic a b` for some `a b : ℤ`, and its image in `ℚ[X]`
  either has Galois group `C₃` (`HasCyclicCubicGaloisGroup`) or splits over `ℚ`.
  (`f` has degree three, so splitting means three linear factors.)
* Normality of a split polynomial is the paper's definition right before the corollary:
  `f = (t−α)(t−β)(t−γ)` is normal if `(α,β,γ)` is normal in the split `C₃`-algebra `ℚ³`,
  i.e. `Cubic.OrbitParametrization.IsNormal α β γ` (the three cyclic permutations are
  `ℚ`-linearly independent). This is required for every ordering of the roots; the
  determinant criterion makes it independent of the ordering anyway.
* The paper does not define "`f` normal" for `f` with Galois group `C₃` explicitly. We
  interpret it as the conclusion of `lemma:cubicimpliesnormal`: every complex root `x`
  of `f` is a normal element of the Galois extension `ℚ(x)/ℚ`
  (`CubicImpliesNormal.IsNormalElement`).
-/

noncomputable section

namespace CubicTargets.Counting.AutomaticallyNormal

open Polynomial
open Cubic.QuadraticCorrespondence.CorrespondencePolynomials
open Cubic.Counting.PolynomialCountData

/-- The paper's `𝓕` in `cor:automaticallyNormal`. -/
def family : Set ℤ[X] :=
  {f | (∃ a b : ℤ, f = traceOneCubic a b) ∧
    (HasCyclicCubicGaloisGroup (f.map (Int.castRingHom ℚ)) ∨
      (f.map (Int.castRingHom ℚ)).Splits)}

/-- `f` is normal: either `f` has Galois group `C₃` and every complex root is a normal
element of `ℚ(x)/ℚ`, or `f` splits over `ℚ` and `(α,β,γ)` is normal in `ℚ³` for every
factorization `f = (t−α)(t−β)(t−γ)` over `ℚ`. -/
def IsNormalPolynomial (f : ℤ[X]) : Prop :=
  (HasCyclicCubicGaloisGroup (f.map (Int.castRingHom ℚ)) ∧
      ∀ x : ℂ, aeval x f = 0 → CubicImpliesNormal.IsNormalElement x) ∨
    ((f.map (Int.castRingHom ℚ)).Splits ∧
      ∀ α β γ : ℚ, f.map (Int.castRingHom ℚ) = (X - C α) * (X - C β) * (X - C γ) →
        Cubic.OrbitParametrization.IsNormal α β γ)

def Claim : Prop := ∀ f ∈ family, IsNormalPolynomial f

end CubicTargets.Counting.AutomaticallyNormal
