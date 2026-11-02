import Cubic.OrbitParametrization.C3AlgebraTwist
import Cubic.OrbitParametrization.SplitAlgebra

/-!
# `example:splitAlgebraNormalElement`

"An element `x` of trace one in the split `C₃`-algebra `K_spl` is normal if and only if `x` either has
distinct coordinates or exactly two identical coordinates. For such a normal element, the pairs `(K_spl,x)` and
`(K_spl',x)` are equivalent if and only if `x` has exactly two identical coordinates
(swapping the identical coordinates gives the required isomorphism); in particular, if
`x` has distinct coordinates then `(K_spl,x)` and `(K_spl',x)` determine different
rational points of `𝒢₁/C₃`, even though `K_spl` and `K_spl'` are isomorphic as
`C₃`-algebras."

**Trace-one hypothesis.** The paper now includes this hypothesis explicitly
(authorized correction, 2026-10-05). Without it the former first sentence fails:
`(-1,0,1)` has distinct coordinates and `(1,1,-2)` exactly two identical
coordinates, yet both have trace zero, so the sum of their conjugates vanishes and they
are not normal: the conjugate evaluation determinant is
`-(x₀+x₁+x₂)/2 · Σ(xᵢ-xⱼ)²` (`conjugates_det_sum_squares`), the negative of
the multiplication determinant in `eqn:normalityDeterminant`. This is proved in
`Cubic.OrbitParametrization.C3Algebra.literal_statement_false`. Since pairs
(`thm:modularInterpretation`) consist of a `C₃`-algebra with a *trace-one* normal
element, the claim below states the corrected example for trace-one `x`
(`HasTraceOne splitAlg x`, i.e. `x₀+x₁+x₂ = 1`), where it is correct.

Modelling:
* `K_spl = splitAlg` (`ZMod 3 → ℚ` with translation action), `K_spl' = splitAlg.twist`
  (action `g ∗ y = g⁻¹ y`), same underlying algebra, so `x` is an element of both.
* "Distinct coordinates" is `Function.Injective x`; "exactly two identical coordinates" is
  `ExactlyTwoEqual x`.
* `(K_spl',x)` is a pair when `(K_spl,x)` is: normality and trace one transfer to the
  twist (second and third conjuncts). The fourth conjunct is stated for arbitrary proofs of
  these properties.
* Rational points of `𝒢₁/C₃ = T` are `ℚ`-algebra maps `quotientFixedRing → ℚ`, and the
  point of a pair is `point` (the bijection of `thm:modularInterpretation`).
* "Isomorphic as `C₃`-algebras" is `C3Alg.Isomorphic`.
-/

namespace CubicTargets.OrbitParametrization.SplitNormalElements

open Cubic.OrbitParametrization.C3Algebra

/-- `x` has exactly two identical coordinates. -/
def ExactlyTwoEqual (x : ZMod 3 → ℚ) : Prop :=
  (∃ i j : ZMod 3, i ≠ j ∧ x i = x j) ∧ ¬ ∀ i j : ZMod 3, x i = x j

def Claim : Prop :=
  (∀ x : ZMod 3 → ℚ, HasTraceOne splitAlg x →
      (IsNormal splitAlg x ↔ Function.Injective x ∨ ExactlyTwoEqual x)) ∧
  (∀ x : ZMod 3 → ℚ, IsNormal splitAlg x → IsNormal splitAlg.twist x) ∧
  (∀ x : ZMod 3 → ℚ, HasTraceOne splitAlg x → HasTraceOne splitAlg.twist x) ∧
  ∀ (x : ZMod 3 → ℚ) (hn : IsNormal splitAlg x) (ht : HasTraceOne splitAlg x)
    (hn' : IsNormal splitAlg.twist x) (ht' : HasTraceOne splitAlg.twist x),
    (Equivalent ⟨splitAlg, x, hn, ht⟩ ⟨splitAlg.twist, x, hn', ht'⟩ ↔ ExactlyTwoEqual x) ∧
    (Function.Injective x →
      point ⟨splitAlg, x, hn, ht⟩ ≠ point ⟨splitAlg.twist, x, hn', ht'⟩ ∧
        splitAlg.Isomorphic splitAlg.twist)

end CubicTargets.OrbitParametrization.SplitNormalElements
