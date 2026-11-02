import Cubic.QuadraticCorrespondence.CorrespondencePolynomials
import Mathlib.Analysis.Complex.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# `lemma:cubicimpliesnormal`

"Let `x ∈ ℂ` be a root of an irreducible polynomial with rational coefficients with
Galois group `C₃` and `t²`-coefficient `−1`. Then `x` is a normal element in the
Galois extension `ℚ(x)/ℚ`."

* The polynomial `f ∈ ℚ[X]` is not assumed monic, and its degree is not assumed:
  irreducibility and Galois group `C₃` force degree three, and this is proved.
* "Galois group `C₃`" is `HasCyclicCubicGaloisGroup f`: the Galois group of the
  splitting field of `f` is isomorphic to `Multiplicative (ZMod 3)`.
* `ℚ(x)` is the intermediate field `ℚ⟮x⟯ ⊆ ℂ`. The phrase "the Galois extension
  `ℚ(x)/ℚ`" is an assertion, so `IsGalois ℚ ℚ⟮x⟯` is part of the conclusion.
* "Normal element": the Galois conjugates `τ x`, `τ ∈ Aut(ℚ(x)/ℚ)`, are linearly
  independent over `ℚ`. Since `ℚ(x)/ℚ` is Galois, the number of conjugates equals
  `[ℚ(x) : ℚ]`, so this is the same as saying they form a basis.
-/

noncomputable section

namespace CubicTargets.Counting.CubicImpliesNormal

open Polynomial IntermediateField
open Cubic.QuadraticCorrespondence.CorrespondencePolynomials

/-- `x` is a normal element of the Galois extension `ℚ(x)/ℚ`: the extension `ℚ⟮x⟯/ℚ`
is Galois, and the conjugates `τ x` (`τ ∈ Aut(ℚ⟮x⟯/ℚ)`) are `ℚ`-linearly independent. -/
def IsNormalElement (x : ℂ) : Prop :=
  IsGalois ℚ ℚ⟮x⟯ ∧
    LinearIndependent ℚ (fun τ : ℚ⟮x⟯ ≃ₐ[ℚ] ℚ⟮x⟯ => τ (AdjoinSimple.gen ℚ x))

def Claim : Prop :=
  ∀ (f : ℚ[X]) (x : ℂ), Irreducible f → HasCyclicCubicGaloisGroup f →
    f.coeff 2 = -1 → aeval x f = 0 → IsNormalElement x

end CubicTargets.Counting.CubicImpliesNormal
