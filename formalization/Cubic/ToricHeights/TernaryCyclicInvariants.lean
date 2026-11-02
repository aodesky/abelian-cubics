import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# The cyclic group `C₃` acting on `ℤ[X,Y,Z]`

The variables are `X = X 0`, `Y = X 1`, `Z = X 2`. The group `C₃` acts by cyclically
permuting them; its generator is `rename (finRotate 3)`, which sends
`X ↦ Y ↦ Z ↦ X`. A polynomial is fixed by `C₃` exactly when it is fixed by this
generator, so the invariant ring is the equalizer of the generator and the identity.
-/

noncomputable section

namespace Cubic.ToricHeights.TernaryCyclicInvariants

open MvPolynomial

/-- The polynomial ring `ℤ[X,Y,Z]`. -/
abbrev TernaryRing := MvPolynomial (Fin 3) ℤ

/-- The generator of `C₃`: the cyclic permutation `X ↦ Y ↦ Z ↦ X` of the variables. -/
def cycle : TernaryRing →ₐ[ℤ] TernaryRing := rename (finRotate 3)

/-- The ring of `C₃`-invariants `ℤ[X,Y,Z]^{C₃}`. -/
def invariants : Subalgebra ℤ TernaryRing := AlgHom.equalizer cycle (AlgHom.id ℤ _)

/-- The cyclic invariant `X²Y + Y²Z + Z²X`. -/
def delta : TernaryRing := X 0 ^ 2 * X 1 + X 1 ^ 2 * X 2 + X 2 ^ 2 * X 0

/-- The homogeneous elementary symmetric polynomial `e_k` in `X,Y,Z`. -/
abbrev e (k : ℕ) : TernaryRing := esymm (Fin 3) ℤ k

end Cubic.ToricHeights.TernaryCyclicInvariants
