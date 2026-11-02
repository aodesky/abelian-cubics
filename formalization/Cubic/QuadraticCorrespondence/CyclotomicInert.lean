import Cubic.QuadraticCorrespondence.CyclotomicBaseChange
import Mathlib.Algebra.Polynomial.SpecificDegree

/-!
# The quadratic cyclotomic algebra at inert primes

For `p ≡ 2 (mod 3)`, the third cyclotomic polynomial has no residue root:
such a root would have order three in the group of order `p-1`.
A p-adic root would have norm one and reduce to a residue root. This proves
irreducibility over the p-adic field and hence that the local tensor
algebra is a field. The norm, integers and residue field at an inert place are
treated in `CyclotomicInertField`, `CyclotomicInertIntegers` and
`CyclotomicInertResidueField`.
-/

noncomputable section

namespace Cubic.QuadraticCorrespondence.CyclotomicInert

open Polynomial CyclotomicLocalAlgebra

variable (p : ℕ) [Fact p.Prime]

/-- The cyclotomic polynomial has no root in the residue field at an inert prime. -/
theorem residue_no_root (hp : p % 3 = 2) (a : ZMod p) : a ^ 2 + a + 1 ≠ 0 := by
  have hp3 : ¬ p ∣ 3 := by
    intro h
    rcases (Nat.dvd_prime Nat.prime_three).mp h with h | h
    · exact (Fact.out : p.Prime).ne_one h
    · omega
  letI : NeZero (3 : ZMod p) := ⟨fun h => hp3 ((ZMod.natCast_eq_zero_iff 3 p).mp h)⟩
  intro ha
  have hprim : IsPrimitiveRoot a 3 := isRoot_cyclotomic_iff.mp (by
    simpa [cyclotomic_three, IsRoot.def] using ha)
  have hd : 3 ∣ p - 1 := by
    rw [hprim.eq_orderOf]
    exact ZMod.orderOf_dvd_card_sub_one (hprim.ne_zero (by decide))
  have := Nat.mod_eq_zero_of_dvd hd
  omega

/-- The residue extension is quadratic. -/
theorem residue_irreducible (hp : p % 3 = 2) : Irreducible (cyclotomic 3 (ZMod p)) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [natDegree_cyclotomic]
    decide
  · intro a
    simpa [cyclotomic_three, IsRoot.def] using residue_no_root p hp a

/-- A root of `X²+X+1` in the p-adic field is integral, because its cube is one. -/
theorem norm_one_of_root {a : ℚ_[p]} (ha : a ^ 2 + a + 1 = 0) : ‖a‖ = 1 := by
  have hc : a ^ 3 = 1 := by linear_combination (a - 1) * ha
  apply (pow_eq_one_iff_of_nonneg (norm_nonneg a) (by decide : 3 ≠ 0)).mp
  simpa only [norm_pow, norm_one] using congrArg norm hc

/-- Reduction rules out a root in the p-adic field. -/
theorem field_no_root (hp : p % 3 = 2) (a : ℚ_[p]) : a ^ 2 + a + 1 ≠ 0 := by
  intro ha
  let b : ℤ_[p] := ⟨a, (norm_one_of_root p ha).le⟩
  have hb : b ^ 2 + b + 1 = 0 := by
    apply Subtype.ext
    exact ha
  apply residue_no_root p hp (PadicInt.toZMod b)
  simpa only [map_add, map_pow, map_one, map_zero] using congrArg PadicInt.toZMod hb

/-- At an inert prime the local cyclotomic quotient is irreducible, rather than
the product algebra occurring at split primes. -/
theorem field_irreducible (hp : p % 3 = 2) : Irreducible (cyclotomic 3 ℚ_[p]) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [natDegree_cyclotomic]
    decide
  · intro a
    simpa [cyclotomic_three, IsRoot.def] using field_no_root p hp a

/-- The local cyclotomic quotient is a field. -/
theorem quotient_isField (hp : p % 3 = 2) : IsField (Model ℚ_[p]) := by
  letI : Fact (Irreducible (cyclotomic 3 ℚ_[p])) := ⟨field_irreducible p hp⟩
  exact Field.toIsField _

/-- The same field property for the base-changed global field. -/
theorem tensor_isField (hp : p % 3 = 2) : IsField (CyclotomicBaseChange.LocalAlgebra ℚ_[p]) := by
  exact (CyclotomicBaseChange.presentation ℚ_[p]).toRingEquiv.isField (quotient_isField p hp)

end Cubic.QuadraticCorrespondence.CyclotomicInert
