import Cubic.ToricHeights.TraceOneCharacters
import Cubic.QuadraticCorrespondence.CyclotomicCoefficients

/-!
# Cubic coefficients from the quotient characters

Construct the characters with exponents `a'=2v₁∨-v₂∨` and
`b'=2v₂∨-v₁∨` on the original augmentation-one group-algebra units. Their
product and sum recover the cubic coefficients of the original coordinates.
The polynomial identity is proved on this cover; descent to the quotient
torus is `DescendedCoefficients`.
-/

noncomputable section

namespace Cubic.QuadraticCorrespondence.CharacterCoefficients

open Cubic.OrbitParametrization
open CyclicGroupAlgebra
open Cubic.ToricHeights.TraceOneCharacters

variable {K : Type*} [Field K]
variable (ζ : K) (hζ : ζ ^ 2 + ζ + 1 = 0)

/-- The pullbacks of the two quotient characters specified by the paper's
cocharacter isomorphism, with their exact integral exponents. -/
def quotientCharacters : traceOneUnits K →* Kˣ × Kˣ :=
  ((firstCharacter ζ hζ) ^ 2 * (secondCharacter ζ hζ)⁻¹).prod
    ((secondCharacter ζ hζ) ^ 2 * (firstCharacter ζ hζ)⁻¹)

theorem quotient_product (g : traceOneUnits K) :
    (quotientCharacters ζ hζ g).1 * (quotientCharacters ζ hζ g).2 =
      firstCharacter ζ hζ g * secondCharacter ζ hζ g := by
  simp [quotientCharacters, pow_succ, mul_comm, mul_left_comm, mul_assoc]

theorem quotient_first_monomial (g : traceOneUnits K) :
    (quotientCharacters ζ hζ g).1 ^ 2 * (quotientCharacters ζ hζ g).2 =
      firstCharacter ζ hζ g ^ 3 := by
  rw [pow_two, mul_assoc, quotient_product]
  let a := firstCharacter ζ hζ g
  let b := secondCharacter ζ hζ g
  change (a ^ 2 * b⁻¹) * (a * b) = a ^ 3
  calc
    _ = (a ^ 2 * a) * (b⁻¹ * b) := by ac_rfl
    _ = _ := by simp [pow_succ]

theorem quotient_second_monomial (g : traceOneUnits K) :
    (quotientCharacters ζ hζ g).1 * (quotientCharacters ζ hζ g).2 ^ 2 =
      secondCharacter ζ hζ g ^ 3 := by
  rw [pow_two, ← mul_assoc, quotient_product]
  let a := firstCharacter ζ hζ g
  let b := secondCharacter ζ hζ g
  change (a * b) * (b ^ 2 * a⁻¹) = b ^ 3
  calc
    _ = (b ^ 2 * b) * (a * a⁻¹) := by ac_rfl
    _ = _ := by simp [pow_succ]

/-- Both quotient characters are trivial on the original cyclic subgroup. -/
theorem quotientCharacters_cyclicUnits (i : Multiplicative (ZMod 3)) :
    quotientCharacters ζ hζ (cyclicUnits K i) = 1 := by
  let a := firstCharacter ζ hζ (cyclicUnits K i)
  let b := secondCharacter ζ hζ (cyclicUnits K i)
  have hb : b = a ^ 2 := by
    apply Units.ext
    change (character K (ζ ^ 2) _ (cyclicUnits K i) : K) =
      (character K ζ _ (cyclicUnits K i) : K) ^ 2
    rw [character_cyclicUnits, character_cyclicUnits, ← pow_mul, ← pow_mul, Nat.mul_comm]
  have ha : a ^ 3 = 1 := by
    apply Units.ext
    change (character K ζ _ (cyclicUnits K i) : K) ^ 3 = 1
    rw [character_cyclicUnits, ← pow_mul, Nat.mul_comm _ 3, pow_mul, root_cube ζ hζ, one_pow]
  change (a ^ 2 * b⁻¹, b ^ 2 * a⁻¹) = 1
  rw [hb]
  apply Prod.ext
  · simp
  · change (a ^ 2) ^ 2 * a⁻¹ = 1
    rw [← pow_mul, show (2 * 2 : ℕ) = 3 + 1 by decide, pow_succ, ha, one_mul, mul_inv_cancel]

theorem quotientCharacters_cyclic_mul (i : Multiplicative (ZMod 3)) (g : traceOneUnits K) :
    quotientCharacters ζ hζ (cyclicUnits K i * g) = quotientCharacters ζ hζ g := by
  rw [map_mul, quotientCharacters_cyclicUnits, one_mul]

/-- Product of the two quotient-character values. -/
def normValue (g : traceOneUnits K) : K :=
  ((quotientCharacters ζ hζ g).1 : K) * ((quotientCharacters ζ hζ g).2 : K)

/-- Sum of the two quotient-character values. -/
def traceValue (g : traceOneUnits K) : K :=
  ((quotientCharacters ζ hζ g).1 : K) + ((quotientCharacters ζ hζ g).2 : K)

theorem normValue_eq (g : traceOneUnits K) :
    normValue ζ hζ g = 1 - 3 * secondCoeff ((g.val : GroupAlgebra K) 0)
      ((g.val : GroupAlgebra K) 1) ((g.val : GroupAlgebra K) 2) := by
  unfold normValue
  rw [← Units.val_mul, quotient_product, Units.val_mul]
  exact character_product ζ hζ g

theorem normValue_mul_traceValue (g : traceOneUnits K) :
    normValue ζ hζ g * traceValue ζ hζ g =
      2 - 9 * secondCoeff ((g.val : GroupAlgebra K) 0)
        ((g.val : GroupAlgebra K) 1) ((g.val : GroupAlgebra K) 2) -
      27 * constantCoeff ((g.val : GroupAlgebra K) 0)
        ((g.val : GroupAlgebra K) 1) ((g.val : GroupAlgebra K) 2) := by
  have h₁ := congrArg Units.val (quotient_first_monomial ζ hζ g)
  have h₂ := congrArg Units.val (quotient_second_monomial ζ hζ g)
  simp only [Units.val_mul, Units.val_pow_eq_pow_val] at h₁ h₂
  calc
    _ = (firstCharacter ζ hζ g : K) ^ 3 + (secondCharacter ζ hζ g : K) ^ 3 := by
      unfold normValue traceValue
      rw [← h₁, ← h₂]
      ring
    _ = _ := character_cubes_sum ζ hζ g

variable [CharZero K]

/-- The linear coefficient from `prop:cyclotomicParametrization`, pulled
back to the original group algebra. -/
theorem secondCoeff_eq (g : traceOneUnits K) :
    secondCoeff ((g.val : GroupAlgebra K) 0) ((g.val : GroupAlgebra K) 1)
      ((g.val : GroupAlgebra K) 2) = (1 - normValue ζ hζ g) / 3 := by
  apply (eq_div_iff (by norm_num : (3 : K) ≠ 0)).mpr
  linear_combination normValue_eq ζ hζ g

/-- The constant coefficient, with the paper's sign `b=-e₃`. -/
theorem constantCoeff_eq (g : traceOneUnits K) :
    constantCoeff ((g.val : GroupAlgebra K) 0) ((g.val : GroupAlgebra K) 1)
      ((g.val : GroupAlgebra K) 2) =
        (normValue ζ hζ g * (3 - traceValue ζ hζ g) - 1) / 27 := by
  apply (eq_div_iff (by norm_num : (27 : K) ≠ 0)).mpr
  linear_combination normValue_mul_traceValue ζ hζ g - 3 * normValue_eq ζ hζ g

/-- When the quotient characters are the two embeddings of `u+vζ`, these
are exactly the coefficient expressions used in the local Fourier cutoffs. -/
theorem coefficients_eq_cyclotomic (g : traceOneUnits K) (u v : K)
    (hcoords : (((quotientCharacters ζ hζ g).1 : K), ((quotientCharacters ζ hζ g).2 : K)) =
      (u + v * ζ, u + v * (-1 - ζ))) :
    secondCoeff ((g.val : GroupAlgebra K) 0) ((g.val : GroupAlgebra K) 1)
      ((g.val : GroupAlgebra K) 2) = CyclotomicCoefficients.linearCoefficient u v ∧
    constantCoeff ((g.val : GroupAlgebra K) 0) ((g.val : GroupAlgebra K) 1)
      ((g.val : GroupAlgebra K) 2) = CyclotomicCoefficients.constantCoefficient u v := by
  have hN : normValue ζ hζ g = CyclotomicCoefficients.normForm u v := by
    unfold normValue
    rw [show ((quotientCharacters ζ hζ g).1 : K) = u + v * ζ from congrArg Prod.fst hcoords,
      show ((quotientCharacters ζ hζ g).2 : K) = u + v * (-1 - ζ) from congrArg Prod.snd hcoords]
    exact CyclotomicCoefficients.linear_mul_conjugate ζ u v hζ
  have hT : traceValue ζ hζ g = CyclotomicCoefficients.traceForm u v := by
    unfold traceValue
    rw [show ((quotientCharacters ζ hζ g).1 : K) = u + v * ζ from congrArg Prod.fst hcoords,
      show ((quotientCharacters ζ hζ g).2 : K) = u + v * (-1 - ζ) from congrArg Prod.snd hcoords]
    exact CyclotomicCoefficients.linear_add_conjugate ζ u v
  rw [secondCoeff_eq ζ hζ g, constantCoeff_eq ζ hζ g, hN, hT]
  exact ⟨rfl, rfl⟩

/-- The explicit norm/trace cubic has the original three coordinates as its
roots. This is a polynomial identity on the trace-one cover, not a claim
that every rational quotient-torus point lifts to this cover. -/
theorem cubic_eq_prod (g : traceOneUnits K) (t : K) :
    traceOneCubic ((1 - normValue ζ hζ g) / 3)
      ((normValue ζ hζ g * (3 - traceValue ζ hζ g) - 1) / 27) t =
        (t - (g.val : GroupAlgebra K) 0) * (t - (g.val : GroupAlgebra K) 1) *
          (t - (g.val : GroupAlgebra K) 2) := by
  rw [← secondCoeff_eq ζ hζ g, ← constantCoeff_eq ζ hζ g]
  exact traceOneCubic_eq_prod _ _ _ t (trace_one K g)

end Cubic.QuadraticCorrespondence.CharacterCoefficients
