import Cubic.OrbitParametrization.CocharacterLattice

/-!
# Cocharacter coordinates for the cyclotomic parametrization

The inverse of `eqn:isoCocharLattices` sends the two standard basis vectors to
`ω` and `γω`. We construct this integral change of basis and verify equivariance
with the Galois actions. This module concerns only the lattices.
-/

namespace Cubic.QuadraticCorrespondence.CocharacterIsomorphism

open Cubic.OrbitParametrization.CocharacterLattice

/-- From coordinates in the cyclotomic basis `(ω, γω)` to the paper's
integral coordinates `(v₁, ω)`. This is the inverse direction to the display. -/
def fromCyclotomic : (ℤ × ℤ) ≃+ (ℤ × ℤ) where
  toFun n := (-n.2, n.1 + 2 * n.2)
  invFun n := (2 * n.1 + n.2, -n.1)
  left_inv n := by ext <;> dsimp <;> ring
  right_inv n := by ext <;> dsimp <;> ring
  map_add' n m := by ext <;> dsimp <;> ring

/-- The map respects conjugation: a swap in the cyclotomic basis. -/
theorem conjugation_fromCyclotomic (n : ℤ × ℤ) :
    conjugation (fromCyclotomic n) = fromCyclotomic n.swap := by
  ext <;> simp [fromCyclotomic, conjugation]
  ring

/-- The ambient ray coordinates of a pair of cyclotomic valuations. -/
theorem coordinates_fromCyclotomic (n : ℤ × ℤ) :
    coordinates (fromCyclotomic n) =
      ((2 * (n.1 : ℚ) + n.2) / 3, ((n.1 : ℚ) + 2 * n.2) / 3) := by
  ext <;> simp [coordinates, fromCyclotomic]
  ring

theorem coordinates_fromCyclotomic_first :
    coordinates (fromCyclotomic (1, 0)) = ω := by
  norm_num [coordinates_fromCyclotomic, ω]

theorem coordinates_fromCyclotomic_second :
    coordinates (fromCyclotomic (0, 1)) = ω.swap := by
  norm_num [coordinates_fromCyclotomic, ω]

/-- The total ray degree is the sum of the two cyclotomic valuations. -/
theorem coordinate_sum_fromCyclotomic (n : ℤ × ℤ) :
    (coordinates (fromCyclotomic n)).1 + (coordinates (fromCyclotomic n)).2 =
      (n.1 : ℚ) + n.2 := by
  rw [coordinates_fromCyclotomic]
  dsimp
  ring

end Cubic.QuadraticCorrespondence.CocharacterIsomorphism
