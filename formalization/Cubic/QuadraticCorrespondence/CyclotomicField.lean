import Cubic.QuadraticCorrespondence.CyclotomicLocalAlgebra
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots

/-!
# The global quadratic cyclotomic field

Use mathlib's cyclotomic number field, with an explicit presentation by
`X²+X+1`. The element `2ζ+1` squares to `-3` and generates the field; this
identifies the presentation with the paper's `E = ℚ(√(-3))`.
-/

noncomputable section

namespace Cubic.QuadraticCorrespondence.CyclotomicField

open Polynomial CyclotomicLocalAlgebra

/-- The paper's quadratic cyclotomic field, using mathlib's field construction. -/
abbrev E := _root_.CyclotomicField 3 ℚ

/-- A chosen primitive cube root, fixing the generator in the presentation. -/
def zeta : E := IsCyclotomicExtension.zeta 3 ℚ E

theorem zeta_primitive : IsPrimitiveRoot zeta 3 :=
  IsCyclotomicExtension.zeta_spec 3 ℚ E

theorem zeta_relation : zeta ^ 2 + zeta + 1 = 0 := by
  simpa [cyclotomic_three] using
    (zeta_primitive.isRoot_cyclotomic (by decide : 0 < 3))

theorem minpoly_zeta : minpoly ℚ zeta = cyclotomic 3 ℚ :=
  (zeta_primitive.minpoly_eq_cyclotomic_of_irreducible
    (cyclotomic.irreducible_rat (by decide))).symm

/-- The polynomial quotient is the cyclotomic field over `ℚ`. -/
def presentation : Model ℚ ≃ₐ[ℚ] E :=
  AdjoinRoot.equiv' (cyclotomic 3 ℚ) (zeta_primitive.powerBasis ℚ)
    (by rw [IsPrimitiveRoot.powerBasis_gen, minpoly_zeta]; exact AdjoinRoot.eval₂_root _)
    (by simp only [IsPrimitiveRoot.powerBasis_gen, cyclotomic_three, map_add,
        map_pow, aeval_X, map_one]; exact zeta_relation)

@[simp]
theorem presentation_root : presentation (AdjoinRoot.root (cyclotomic 3 ℚ)) = zeta := by
  simp [presentation, AdjoinRoot.equiv'_apply, IsPrimitiveRoot.powerBasis_gen]

/-- The global degree used to weight the splitting-field places in the height. -/
theorem finrank_eq_two : Module.finrank ℚ E = 2 := by
  rw [← presentation.toLinearEquiv.finrank_eq]
  exact CyclotomicLocalAlgebra.finrank_model

/-- A square root of `-3` in the cyclotomic presentation. -/
def sqrtNegThree : E := 2 * zeta + 1

theorem sqrtNegThree_sq : sqrtNegThree ^ 2 = -3 := by
  dsimp [sqrtNegThree]
  linear_combination 4 * zeta_relation

/-- The square root generates the entire field, not just a subfield. -/
theorem adjoin_sqrtNegThree : Algebra.adjoin ℚ ({sqrtNegThree} : Set E) = ⊤ := by
  apply (zeta_primitive.powerBasis ℚ).adjoin_eq_top_of_gen_mem_adjoin
  rw [IsPrimitiveRoot.powerBasis_gen, Algebra.adjoin_singleton_eq_range_aeval]
  refine ⟨C (1 / 2 : ℚ) * (X - 1), ?_⟩
  simp [sqrtNegThree]

end Cubic.QuadraticCorrespondence.CyclotomicField
