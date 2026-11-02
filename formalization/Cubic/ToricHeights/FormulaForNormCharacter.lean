import CubicTargets.ToricHeights.FormulaForNormCharacter

/-!
# Proof of `eqn:formulaForNormCharacter`

The paper's computation "using the formulas from §ToricDescription":
`χ^{a'+b'} = χ^{v₁^∨+v₂^∨}` pulls back to `χ₁χ₂/χ₀²`, and on `g = u v₀' + v v₁' + w v₂'`
the characters take the values `χ₀(g) = u`, `χ₁(g) = v`, `χ₂(g) = w` (`idempotent_values`);
in coordinates `χ₀ = X+Y+Z`, `χ₁ = X+ζY+ζ²Z`, `χ₂ = X+ζ²Y+ζZ`. The numerator is
`TraceOneCharacters.eigenvalue_product`.
-/

noncomputable section

namespace Cubic.ToricHeights.FormulaForNormCharacter

open Cubic.OrbitParametrization.CyclicGroupAlgebra
open Cubic.ToricHeights.TraceOneCharacters
open Cubic.QuadraticCorrespondence
open CubicTargets.ToricHeights.FormulaForNormCharacter

variable {K : Type} [Field K] [CharZero K]

omit [CharZero K] in
theorem coordinates_zero (x y z : K) : coordinates K x y z 0 = x := by
  simp [coordinates, show (2 : ZMod 3) ≠ 0 by decide]

omit [CharZero K] in
theorem coordinates_one (x y z : K) : coordinates K x y z 1 = y := by
  simp [coordinates, show (2 : ZMod 3) ≠ 1 by decide]

omit [CharZero K] in
theorem coordinates_two (x y z : K) : coordinates K x y z 2 = z := by
  simp [coordinates, show (0 : ZMod 3) ≠ 2 by decide, show (1 : ZMod 3) ≠ 2 by decide]

/-- The idempotent coordinates are the three character values. -/
theorem idempotent_values (ζ : K) (hζ : ζ ^ 2 + ζ + 1 = 0) (g : GroupAlgebra K) (u v w : K)
    (hg : g = u • idempotent₀ + v • idempotent₁ ζ + w • idempotent₂ ζ) :
    g 0 + g 1 + g 2 = u ∧ g 0 + ζ * g 1 + ζ ^ 2 * g 2 = v ∧
      g 0 + ζ ^ 2 * g 1 + ζ * g 2 = w := by
  have h0 : g 0 = u / 3 + v / 3 + w / 3 := by
    rw [hg]
    simp [idempotent₀, idempotent₁, idempotent₂, coordinates_zero]
    ring
  have h1 : g 1 = u / 3 + v * ζ ^ 2 / 3 + w * ζ / 3 := by
    rw [hg]
    simp [idempotent₀, idempotent₁, idempotent₂, coordinates_one]
    ring
  have h2 : g 2 = u / 3 + v * ζ / 3 + w * ζ ^ 2 / 3 := by
    rw [hg]
    simp [idempotent₀, idempotent₁, idempotent₂, coordinates_two]
    ring
  rw [h0, h1, h2]
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (v / 3 + w / 3) * hζ
  · linear_combination (u / 3 + 2 * v * (ζ - 1) / 3 + w * (ζ ^ 2 - ζ + 1) / 3) * hζ
  · linear_combination (u / 3 + v * (ζ ^ 2 - ζ + 1) / 3 + 2 * w * (ζ - 1) / 3) * hζ

omit [CharZero K] in
theorem augmentation_ne_zero (g : (GroupAlgebra K)ˣ) : augmentation K (g : GroupAlgebra K) ≠ 0 :=
  (Units.map (augmentation K).toMonoidHom g).ne_zero

omit [CharZero K] in
theorem normalize_val (g : (GroupAlgebra K)ˣ) :
    (((normalize g : traceOneUnits K) : (GroupAlgebra K)ˣ) : GroupAlgebra K) =
      algebraMap K (GroupAlgebra K) (augmentation K (g : GroupAlgebra K))⁻¹ *
        (g : GroupAlgebra K) := by
  change algebraMap K (GroupAlgebra K) ((Units.map (augmentation K).toMonoidHom g)⁻¹ : Kˣ) *
    (g : GroupAlgebra K) = _
  rw [Units.val_inv_eq_inv_val]
  rfl

theorem first_normalize (ζ : K) (hζ : ζ ^ 2 + ζ + 1 = 0) (g : (GroupAlgebra K)ˣ) :
    ((firstCharacter ζ hζ (normalize g) : Kˣ) : K) =
      (augmentation K (g : GroupAlgebra K))⁻¹ *
        ((g : GroupAlgebra K) 0 + ζ * (g : GroupAlgebra K) 1 + ζ ^ 2 * (g : GroupAlgebra K) 2) := by
  rw [firstCharacter, character_val, normalize_val]
  simp only [← evaluation_coefficients K ζ (root_cube ζ hζ), map_mul, AlgHom.commutes]
  rw [evaluation_coefficients, Algebra.algebraMap_self, RingHom.id_apply]
  ring

theorem second_normalize (ζ : K) (hζ : ζ ^ 2 + ζ + 1 = 0) (g : (GroupAlgebra K)ˣ) :
    ((secondCharacter ζ hζ (normalize g) : Kˣ) : K) =
      (augmentation K (g : GroupAlgebra K))⁻¹ *
        ((g : GroupAlgebra K) 0 + ζ ^ 2 * (g : GroupAlgebra K) 1 + ζ * (g : GroupAlgebra K) 2) := by
  rw [secondCharacter_val, normalize_val]
  have h := evaluation_coefficients K (ζ ^ 2) (square_root_cube ζ hζ)
    (algebraMap K (GroupAlgebra K) (augmentation K (g : GroupAlgebra K))⁻¹ * (g : GroupAlgebra K))
  rw [map_mul, AlgHom.commutes, evaluation_coefficients, ← pow_mul,
    root_fourth ζ hζ] at h
  rw [← h, Algebra.algebraMap_self, RingHom.id_apply]
  ring

omit [CharZero K] in
theorem groupCharacter_val (ζ : K) (hζ : ζ ^ 2 + ζ + 1 = 0) (m : ℤ × ℤ) (g : (GroupAlgebra K)ˣ) :
    ((groupCharacter ζ hζ m g : Kˣ) : K) =
      ((firstCharacter ζ hζ (normalize g) : Kˣ) : K) ^ (CharacterLattice.pullback m).1 *
        ((secondCharacter ζ hζ (normalize g) : Kˣ) : K) ^ (CharacterLattice.pullback m).2 := by
  simp only [groupCharacter, CubicTargets.ToricHeights.FormulaForNormCharacter.character,
    MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.zpow_apply, Units.val_mul,
    Units.val_zpow_eq_zpow_val]

theorem «eqn:formulaForNormCharacter» : CubicTargets.ToricHeights.FormulaForNormCharacter.Claim := by
  intro K _ _ ζ hζ g u v w hg
  obtain ⟨hu, hv, hw⟩ := idempotent_values ζ hζ (g : GroupAlgebra K) u v w hg
  have ha : augmentation K (g : GroupAlgebra K) = u := by
    rw [augmentation_coefficients, hu]
  refine ⟨?_, ?_, ?_⟩
  · rw [groupCharacter_val, first_normalize, second_normalize, ha, hv, hw]
    simp only [CharacterLattice.pullback, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    norm_num
    ring
  · rw [hu, hv, hw]
  · have hp := eigenvalue_product ζ hζ ((g : GroupAlgebra K) 0) ((g : GroupAlgebra K) 1)
      ((g : GroupAlgebra K) 2)
    unfold Cubic.OrbitParametrization.secondCoeff at hp
    simp only [e₁, e₂]
    congr 1
    linear_combination hp

end Cubic.ToricHeights.FormulaForNormCharacter
