import Cubic.OrbitParametrization.CyclicGroupAlgebra
import Cubic.OrbitParametrization.TraceOne
import Mathlib.Tactic.LinearCombination

/-!
# Character formulas on the original trace-one group algebra

The two nontrivial cyclic characters have product `1-3e₂` and sum of cubes
`2-9e₂+27e₃`. These are the character identities used in
`lemma:heightformula` and `prop:cyclotomicParametrization`, proved on the
augmentation-one unit group. Their evaluation on the quotient torus is in
`WeightVectors`, and the global-section statement is `lemma:heightformula`
(`HeightFormula`).
-/

noncomputable section

namespace Cubic.ToricHeights.TraceOneCharacters

open Cubic.OrbitParametrization
open CyclicGroupAlgebra

variable {R : Type*} [CommRing R]

theorem root_cube (ζ : R) (hζ : ζ ^ 2 + ζ + 1 = 0) : ζ ^ 3 = 1 := by
  linear_combination (ζ - 1) * hζ

theorem root_fourth (ζ : R) (hζ : ζ ^ 2 + ζ + 1 = 0) : ζ ^ 4 = ζ := by
  rw [show (4 : ℕ) = 3 + 1 by rfl, pow_succ, root_cube ζ hζ, one_mul]

theorem square_root_cube (ζ : R) (hζ : ζ ^ 2 + ζ + 1 = 0) : (ζ ^ 2) ^ 3 = 1 := by
  rw [← pow_mul, show 2 * 3 = 3 * 2 by rfl, pow_mul, root_cube ζ hζ, one_pow]

/-- The polynomial numerator in `eqn:formulaForNormCharacter`. -/
theorem eigenvalue_product (ζ : R) (hζ : ζ ^ 2 + ζ + 1 = 0) (x y z : R) :
    (x + y * ζ + z * ζ ^ 2) * (x + y * ζ ^ 2 + z * ζ) =
      (x + y + z) ^ 2 - 3 * secondCoeff x y z := by
  have hsq : ζ ^ 2 = -1 - ζ := by linear_combination hζ
  rw [hsq]
  unfold secondCoeff
  linear_combination -(y - z) ^ 2 * hζ

/-- The sum of the two cubic characters, before specializing to trace one. -/
theorem eigenvalue_cubes_sum (ζ : R) (hζ : ζ ^ 2 + ζ + 1 = 0) (x y z : R) :
    (x + y * ζ + z * ζ ^ 2) ^ 3 + (x + y * ζ ^ 2 + z * ζ) ^ 3 =
      2 * (x + y + z) ^ 3 - 9 * (x + y + z) * secondCoeff x y z + 27 * x * y * z := by
  have hsq : ζ ^ 2 = -1 - ζ := by linear_combination hζ
  rw [hsq]
  unfold secondCoeff
  linear_combination 3 * (2 * x - y - z) * (y - z) ^ 2 * hζ

/-- The first nontrivial character, on the group-algebra units. -/
def firstCharacter (ζ : R) (hζ : ζ ^ 2 + ζ + 1 = 0) : traceOneUnits R →* Rˣ :=
  character R ζ (root_cube ζ hζ)

/-- The conjugate character. -/
def secondCharacter (ζ : R) (hζ : ζ ^ 2 + ζ + 1 = 0) : traceOneUnits R →* Rˣ :=
  character R (ζ ^ 2) (square_root_cube ζ hζ)

theorem secondCharacter_val (ζ : R) (hζ : ζ ^ 2 + ζ + 1 = 0) (g : traceOneUnits R) :
    (secondCharacter ζ hζ g : R) =
      (g.val : GroupAlgebra R) 0 + (g.val : GroupAlgebra R) 1 * ζ ^ 2 +
        (g.val : GroupAlgebra R) 2 * ζ := by
  rw [secondCharacter, character_val, ← pow_mul, root_fourth ζ hζ]

/-- The invariant norm character on the trace-one cover is `1-3e₂`. -/
theorem character_product (ζ : R) (hζ : ζ ^ 2 + ζ + 1 = 0) (g : traceOneUnits R) :
    (firstCharacter ζ hζ g : R) * (secondCharacter ζ hζ g : R) =
      1 - 3 * secondCoeff ((g.val : GroupAlgebra R) 0)
        ((g.val : GroupAlgebra R) 1) ((g.val : GroupAlgebra R) 2) := by
  rw [firstCharacter, character_val, secondCharacter_val, eigenvalue_product ζ hζ,
    trace_one R g, one_pow]

/-- The sum of the two invariant cubic characters is `2-9e₂+27e₃`. -/
theorem character_cubes_sum (ζ : R) (hζ : ζ ^ 2 + ζ + 1 = 0) (g : traceOneUnits R) :
    (firstCharacter ζ hζ g : R) ^ 3 + (secondCharacter ζ hζ g : R) ^ 3 =
      2 - 9 * secondCoeff ((g.val : GroupAlgebra R) 0)
        ((g.val : GroupAlgebra R) 1) ((g.val : GroupAlgebra R) 2) -
      27 * constantCoeff ((g.val : GroupAlgebra R) 0)
        ((g.val : GroupAlgebra R) 1) ((g.val : GroupAlgebra R) 2) := by
  rw [firstCharacter, character_val, secondCharacter_val, eigenvalue_cubes_sum ζ hζ,
    trace_one R g]
  simp only [one_pow, mul_one, constantCoeff]
  ring

end Cubic.ToricHeights.TraceOneCharacters
