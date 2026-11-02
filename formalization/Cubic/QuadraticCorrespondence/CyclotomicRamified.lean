import Cubic.QuadraticCorrespondence.CyclotomicInert

/-!
# The cyclotomic field at the exceptional prime

The polynomial `X²+X+1` has no root modulo nine. A root over `ℚ₃` would
have norm one and hence reduce modulo nine, so the local cyclotomic algebra
is a field also at three. Reduction modulo three alone would not prove this.
-/

noncomputable section

namespace Cubic.QuadraticCorrespondence.CyclotomicRamified

open Polynomial CyclotomicLocalAlgebra

/-- The repeated root modulo three does not lift to a root modulo nine. -/
theorem modNine_no_root : ∀ a : ZMod (3 ^ 2), a ^ 2 + a + 1 ≠ 0 := by decide

theorem field_no_root (a : ℚ_[3]) : a ^ 2 + a + 1 ≠ 0 := by
  intro ha
  let b : ℤ_[3] := ⟨a, (CyclotomicInert.norm_one_of_root 3 ha).le⟩
  have hb : b ^ 2 + b + 1 = 0 := by
    apply Subtype.ext
    exact ha
  apply modNine_no_root (PadicInt.toZModPow 2 b)
  simpa only [map_add, map_pow, map_one, map_zero] using
    congrArg (PadicInt.toZModPow 2) hb

/-- Irreducibility at three. -/
theorem field_irreducible : Irreducible (cyclotomic 3 ℚ_[3]) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [natDegree_cyclotomic]
    decide
  · intro a
    simpa [cyclotomic_three, IsRoot.def] using field_no_root a

theorem quotient_isField : IsField (Model ℚ_[3]) := by
  letI : Fact (Irreducible (cyclotomic 3 ℚ_[3])) := ⟨field_irreducible⟩
  exact Field.toIsField _

/-- The base change of the global field is a field at three. -/
theorem tensor_isField : IsField (CyclotomicBaseChange.LocalAlgebra ℚ_[3]) :=
  (CyclotomicBaseChange.presentation ℚ_[3]).toRingEquiv.isField quotient_isField

end Cubic.QuadraticCorrespondence.CyclotomicRamified
