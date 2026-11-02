import Cubic.QuadraticCorrespondence.CocharacterIsomorphism

/-!
# The character sublattice of the cyclic quotient

The quotient basis `a'=2v₁∨-v₂∨`, `b'=2v₂∨-v₁∨` pulls back to an index-three
sublattice of the cover's character lattice. Its image is exactly the exponents
with `3 ∣ m₁+2m₂`, and exactly the integral characters on the paper's enlarged
cocharacter lattice. This identifies the lattice used in the invariant Laurent ring.
-/

namespace Cubic.QuadraticCorrespondence.CharacterLattice

open Cubic.OrbitParametrization.CocharacterLattice
open CocharacterIsomorphism

/-- Pullback of the quotient's character basis to the two cover characters. -/
def pullback : (ℤ × ℤ) →+ (ℤ × ℤ) where
  toFun n := (2 * n.1 - n.2, -n.1 + 2 * n.2)
  map_zero' := by simp
  map_add' n m := by ext <;> dsimp <;> ring

theorem pullback_injective : Function.Injective pullback := by
  intro n m h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  dsimp [pullback] at h₁ h₂
  ext <;> omega

/-- Triviality of a cover character on `C₃` is precisely this congruence. -/
theorem mem_range_pullback (m : ℤ × ℤ) :
    m ∈ Set.range pullback ↔ (3 : ℤ) ∣ m.1 + 2 * m.2 := by
  constructor
  · rintro ⟨n, rfl⟩
    refine ⟨n.2, ?_⟩
    dsimp [pullback]
    ring
  · rintro ⟨k, hk⟩
    refine ⟨(2 * k - m.2, k), ?_⟩
    ext <;> dsimp [pullback] <;> omega

theorem pullback_swap (m : ℤ × ℤ) : pullback m.swap = (pullback m).swap := by
  ext <;> dsimp [pullback] <;> ring

/-- The character and cocharacter changes of basis are dual. -/
theorem pairing_fromCyclotomic (m n : ℤ × ℤ) :
    ((pullback m).1 : ℚ) * (coordinates (fromCyclotomic n)).1 +
      ((pullback m).2 : ℚ) * (coordinates (fromCyclotomic n)).2 =
        (m.1 : ℚ) * n.1 + (m.2 : ℚ) * n.2 := by
  rw [coordinates_fromCyclotomic]
  simp [pullback]
  ring

/-- This is the dual of the enlarged cocharacter lattice. -/
theorem mem_range_iff_integral_pairings (m : ℤ × ℤ) :
    m ∈ Set.range pullback ↔ ∀ n : ℤ × ℤ, ∃ k : ℤ,
      (m.1 : ℚ) * (coordinates n).1 + (m.2 : ℚ) * (coordinates n).2 = k := by
  constructor
  · rintro ⟨r, rfl⟩ n
    refine ⟨(2 * r.1 - r.2) * n.1 + r.1 * n.2, ?_⟩
    simp [pullback, coordinates]
    ring
  · intro h
    obtain ⟨k, hk⟩ := h (0, 1)
    have hk' : 2 * m.1 + m.2 = 3 * k := by
      have hq : 2 * (m.1 : ℚ) + m.2 = 3 * k := by
        dsimp [coordinates] at hk
        linarith
      exact_mod_cast hq
    apply (mem_range_pullback m).mpr
    exact ⟨m.1 + m.2 - k, by omega⟩

end Cubic.QuadraticCorrespondence.CharacterLattice
