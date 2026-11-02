import Cubic.PoissonSummation.CyclotomicPrincipalGenerators
import Cubic.QuadraticCorrespondence.RationalParameterBaseChange
import Cubic.ToricHeights.SplitQuotientLogarithm
import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Principal generators separating the two split places

The ideal `(p,ζ-r)`, where `r` is the residue of the specified first local
embedding of `ζ`, is principal by the class-number-one theorem. Its generator
has valuation one at that place and zero at the conjugate place. The norm
formula in `CyclotomicPrincipalGenerators` also makes it a unit away from `p`.
This constructs the arithmetic input; its transfer to arbitrary finite
adelic valuation data is separate.
-/

noncomputable section

namespace Cubic.PoissonSummation.CyclotomicSplitGenerators

open Cubic.QuadraticCorrespondence Cubic.ToricHeights
open CyclotomicIntegerUnits CyclotomicPrincipalGenerators RationalParameterBaseChange
open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 1)]

def firstEmbedding : Integers →+* ℚ_[p] :=
  (SplitQuotientLogarithm.place p).comp
    ((fieldInclusion ℚ_[p]).toRingHom.comp (algebraMap Integers CyclotomicField.E))

def secondEmbedding : Integers →+* ℚ_[p] :=
  (SplitQuotientLogarithm.secondPlace p).comp
    ((fieldInclusion ℚ_[p]).toRingHom.comp (algebraMap Integers CyclotomicField.E))

theorem embeddings_zeta :
    secondEmbedding p zetaInteger = -1 - firstEmbedding p zetaInteger := by
  have h := SplitQuotientLogarithm.splitting_zeta p
  exact (congrArg Prod.snd h).trans (congrArg (fun z => -1 - z) (congrArg Prod.fst h)).symm

def rootInteger : ℤ_[p] := ⟨firstEmbedding p zetaInteger,
  norm_integer_image (firstEmbedding p) zetaInteger⟩

def residue : ℕ := (rootInteger p).zmodRepr

theorem first_sub_residue_lt_one : ‖firstEmbedding p zetaInteger - residue p‖ < 1 := by
  exact PadicInt.norm_sub_zmodRepr_lt_one (rootInteger p)

theorem first_sub_residue_le :
    ‖firstEmbedding p zetaInteger - residue p‖ ≤ (p : ℝ)⁻¹ := by
  have h := (Padic.norm_lt_pow_iff_norm_le_pow_sub_one
    (firstEmbedding p zetaInteger - (residue p : ℚ_[p])) 0).mp
      (by simpa only [zpow_zero] using first_sub_residue_lt_one p)
  simpa only [zero_sub, zpow_neg_one] using h

theorem embeddings_difference_norm :
    ‖firstEmbedding p zetaInteger - secondEmbedding p zetaInteger‖ = 1 := by
  let z := firstEmbedding p zetaInteger
  have hz : z ^ 2 + z + 1 = 0 := by
    have hz' : zetaInteger ^ 2 + zetaInteger + 1 = 0 := by
      apply (show Function.Injective (algebraMap Integers CyclotomicField.E)
        from Subtype.val_injective)
      simpa only [map_add, map_pow, map_one, map_zero] using CyclotomicField.zeta_relation
    simpa only [map_add, map_pow, map_one, map_zero] using congrArg (firstEmbedding p) hz'
  have hp3 : p ≠ 3 := by have := (Fact.out : p % 3 = 1); omega
  have hn3 : ‖(3 : ℚ_[p])‖ = 1 := by
    apply Padic.norm_natCast_eq_one_iff.mpr
    exact (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
      (fun hd => hp3 (((Nat.prime_three.dvd_iff_eq (Fact.out : p.Prime).ne_one).mp hd).symm))
  rw [embeddings_zeta]
  change ‖z - (-1 - z)‖ = 1
  apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by decide : 2 ≠ 0)).mp
  rw [← norm_pow, show (z - (-1 - z)) ^ 2 = -3 by linear_combination 4 * hz,
    norm_neg, hn3]

theorem second_sub_residue_norm : ‖secondEmbedding p zetaInteger - residue p‖ = 1 := by
  have hb : ‖secondEmbedding p zetaInteger - residue p‖ ≤ 1 := by
    simpa only [map_sub, map_natCast] using
      norm_integer_image (secondEmbedding p) (zetaInteger - residue p)
  apply le_antisymm hb
  by_contra hn
  have ht := max_lt (first_sub_residue_lt_one p) (lt_of_not_ge hn)
  have hd := Padic.nonarchimedean (firstEmbedding p zetaInteger - (residue p : ℚ_[p]))
    (-(secondEmbedding p zetaInteger - (residue p : ℚ_[p])))
  rw [show firstEmbedding p zetaInteger - residue p +
      -(secondEmbedding p zetaInteger - residue p) =
      firstEmbedding p zetaInteger - secondEmbedding p zetaInteger by ring,
    embeddings_difference_norm, norm_neg] at hd
  exact (not_lt_of_ge hd) ht

def generator : Integers := splitGenerator p (residue p)

theorem generator_ne_zero : generator p ≠ 0 :=
  splitGenerator_ne_zero p (residue p) (Fact.out : p.Prime).ne_zero

/-- Exactly one valuation step in the first factor, using the base-field norm convention. -/
theorem first_generator_norm : ‖firstEmbedding p (generator p)‖ = (p : ℝ)⁻¹ := by
  rw [generator, norm_splitGenerator, Padic.norm_p, max_eq_left (first_sub_residue_le p)]

theorem second_generator_norm : ‖secondEmbedding p (generator p)‖ = 1 := by
  rw [generator, norm_splitGenerator, second_sub_residue_norm,
    max_eq_right (Padic.norm_p_lt_one (p := p)).le]

end Cubic.PoissonSummation.CyclotomicSplitGenerators
