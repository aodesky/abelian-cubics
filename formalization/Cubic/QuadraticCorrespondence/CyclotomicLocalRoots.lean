import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic.LinearCombination

/-!
# Cyclotomic roots at split rational primes

For `p ≡ 1 (mod 3)`, Cauchy's theorem gives a primitive cube root in `𝔽_p`.
Mathlib's Hensel lemma lifts its simple cyclotomic root to `ℤ_[p]`,
and hence to `ℚ_[p]`. This is the arithmetic input for the local algebra's
splitting.
-/

noncomputable section

namespace Cubic.QuadraticCorrespondence.CyclotomicLocalRoots

open Polynomial

variable (p : ℕ) [Fact p.Prime]

theorem reduction_eq_zero_iff (x : ℤ_[p]) :
    PadicInt.toZMod x = 0 ↔ ‖x‖ < 1 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal,
    PadicInt.mem_nonunits]

theorem norm_eq_one_of_reduction_ne_zero {x : ℤ_[p]} (hx : PadicInt.toZMod x ≠ 0) :
    ‖x‖ = 1 := by
  apply le_antisymm (PadicInt.norm_le_one x)
  exact le_of_not_gt (fun h => hx ((reduction_eq_zero_iff p x).mpr h))

/-- The third cyclotomic polynomial has a simple root in the residue field. -/
theorem residue_root (hp : p % 3 = 1) :
    ∃ a : ZMod p, a ^ 2 + a + 1 = 0 ∧ 2 * a + 1 ≠ 0 := by
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd : 3 ∣ Fintype.card (ZMod p)ˣ := by
    rw [ZMod.card_units]
    apply Nat.dvd_of_mod_eq_zero
    omega
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card (G := (ZMod p)ˣ) 3 hdvd
  have hprim : IsPrimitiveRoot (u : ZMod p) 3 :=
    IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.iff_orderOf.mpr hu)
  have hroot : (u : ZMod p) ^ 2 + u + 1 = 0 := by
    simpa [cyclotomic_three, IsRoot.def] using hprim.isRoot_cyclotomic (by decide)
  refine ⟨u, hroot, ?_⟩
  intro hderiv
  have h3 : (3 : ZMod p) = 0 := by
    linear_combination 4 * hroot - (2 * (u : ZMod p) + 1) * hderiv
  have hd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp h3
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
  · exact (Fact.out : p.Prime).ne_one h
  · omega

/-- Lift the simple residue root using mathlib's p-adic Hensel theorem. -/
theorem integral_root (hp : p % 3 = 1) : ∃ ζ : ℤ_[p], ζ ^ 2 + ζ + 1 = 0 := by
  obtain ⟨a₀, ha₀, hda₀⟩ := residue_root p hp
  obtain ⟨a, ha⟩ := ZMod.ringHom_surjective (PadicInt.toZMod : ℤ_[p] →+* ZMod p) a₀
  let F : Polynomial ℤ_[p] := X ^ 2 + X + 1
  have hf : F.aeval a = a ^ 2 + a + 1 := by simp [F]
  have hd : F.derivative.aeval a = 2 * a + 1 := by
    simp only [F, derivative_X_pow, derivative_X, derivative_one,
      map_add, map_mul, map_pow, aeval_C, aeval_X, map_one, map_zero,
      Algebra.algebraMap_self, RingHom.id_apply]
    ring
  have hsmall : ‖F.aeval a‖ < 1 := by
    apply (reduction_eq_zero_iff p _).mp
    simpa [hf, map_add, map_pow, ha] using ha₀
  have hunit : ‖F.derivative.aeval a‖ = 1 := by
    apply norm_eq_one_of_reduction_ne_zero
    simpa [hd, map_add, map_mul, map_ofNat, ha] using hda₀
  obtain ⟨ζ, hζ, _⟩ := hensels_lemma (p := p) (F := F) (a := a)
    (by simpa only [hunit, one_pow] using hsmall)
  exact ⟨ζ, by simpa [F] using hζ⟩

/-- The p-adic field contains a root of the third cyclotomic polynomial. -/
theorem field_root (hp : p % 3 = 1) : ∃ ζ : ℚ_[p], ζ ^ 2 + ζ + 1 = 0 := by
  obtain ⟨ζ, hζ⟩ := integral_root p hp
  exact ⟨ζ, by simpa using congrArg (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p]) hζ⟩

end Cubic.QuadraticCorrespondence.CyclotomicLocalRoots
