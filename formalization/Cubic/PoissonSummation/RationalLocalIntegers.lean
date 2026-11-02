import Cubic.QuadraticCorrespondence.RationalParameterBaseChange
import Cubic.PoissonSummation.RationalAdelicEmbedding
import Cubic.QuadraticCorrespondence.CyclotomicInertIntegers
import Cubic.QuadraticCorrespondence.CyclotomicRamifiedIntegers

/-!
# Cyclotomic coefficients of compact rational points

The paper's assertion that a point is an integer unit if it is a unit at every
finite place is expanded in the common basis `1,ζ`. The split, inert and
ramified conditions all bound the same rational coefficients, including at
three where the basis is integral but not orthonormal.
-/

noncomputable section

namespace Cubic.PoissonSummation.RationalLocalIntegers

open Cubic.QuadraticCorrespondence Cubic.ToricHeights
open CyclotomicField RationalParameterBaseChange RationalAdelicEmbedding
open scoped TensorProduct RationalQuotientGroup

variable (p : ℕ) [Fact p.Prime]

/-- Away from three, the two split embeddings recover integral basis coefficients. -/
theorem split_coefficients_le_one (hp : p ≠ 3) (z a b : ℚ_[p])
    (hz : z ^ 2 + z + 1 = 0)
    (h₁ : ‖a + b * z‖ ≤ 1) (h₂ : ‖a + b * (-1 - z)‖ ≤ 1) :
    ‖a‖ ≤ 1 ∧ ‖b‖ ≤ 1 := by
  have hz3 : z ^ 3 = 1 := by linear_combination (z - 1) * hz
  have hnz : ‖z‖ = 1 :=
    (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by decide : 3 ≠ 0)).mp
      (by simpa only [norm_pow, norm_one] using congrArg norm hz3)
  have hthree : ‖(3 : ℚ_[p])‖ = 1 := by
    apply Padic.norm_natCast_eq_one_iff.mpr
    exact (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
      (fun hd => hp (((Nat.prime_three.dvd_iff_eq (Fact.out : p.Prime).ne_one).mp hd).symm))
  have hd : ‖2 * z + 1‖ = 1 := by
    apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by decide : 2 ≠ 0)).mp
    rw [← norm_pow, show (2 * z + 1) ^ 2 = -3 by linear_combination 4 * hz,
      norm_neg, hthree]
  have hb : ‖b‖ ≤ 1 := by
    have he : b * (2 * z + 1) = (a + b * z) - (a + b * (-1 - z)) := by ring
    calc
      ‖b‖ = ‖b * (2 * z + 1)‖ := by rw [norm_mul, hd, mul_one]
      _ = ‖(a + b * z) - (a + b * (-1 - z))‖ := congrArg norm he
      _ ≤ max ‖a + b * z‖ ‖a + b * (-1 - z)‖ := by
        simpa only [sub_eq_add_neg, norm_neg] using Padic.nonarchimedean
          (a + b * z) (-(a + b * (-1 - z)))
      _ ≤ 1 := max_le h₁ h₂
  refine ⟨?_, hb⟩
  have h := Padic.nonarchimedean (a + b * z) (-(b * z))
  simpa only [add_neg_cancel_right, norm_neg, norm_mul, hnz, mul_one] using
    h.trans (max_le h₁ (by simpa only [norm_neg, norm_mul, hnz, mul_one] using hb))

theorem split_parameter_linear [Fact (p % 3 = 1)] (P : Points) (a b : ℚ)
    (hP : (parameterEquiv P : E) = algebraMap ℚ E a + algebraMap ℚ E b * zeta) :
    let z := Classical.choose (CyclotomicLocalRoots.field_root p Fact.out)
    (((SplitQuotientLogarithm.localPoint p (baseChange ℚ_[p] P)).1 : ℚ_[p]),
      ((SplitQuotientLogarithm.localPoint p (baseChange ℚ_[p] P)).2 : ℚ_[p])) =
      ((a : ℚ_[p]) + (b : ℚ_[p]) * z, (a : ℚ_[p]) + (b : ℚ_[p]) * (-1 - z)) := by
  have h := map_parameter_linear ℚ_[p] (SplitQuotientLogarithm.splitting p).toAlgHom P a b hP
  simp only [AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe] at h
  rw [SplitQuotientLogarithm.splitting_zeta] at h
  exact h

theorem inert_parameter_linear [Fact (p % 3 = 2)] (P : Points) (a b : ℚ)
    (hP : (parameterEquiv P : E) = algebraMap ℚ E a + algebraMap ℚ E b * zeta) :
    (InertQuotientLogarithm.localPoint p (baseChange ℚ_[p] P) : CyclotomicInertField.Extension p) =
      CyclotomicInertField.linear p (a : ℚ_[p]) (b : ℚ_[p]) := by
  have h := map_parameter_linear ℚ_[p] (InertQuotientLogarithm.place p).toAlgHom P a b hP
  simpa only [AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe,
    InertQuotientLogarithm.place_zeta, CyclotomicInertField.linear,
    map_ratCast, eq_ratCast] using h

theorem ramified_parameter_linear (P : Points) (a b : ℚ)
    (hP : (parameterEquiv P : E) = algebraMap ℚ E a + algebraMap ℚ E b * zeta) :
    (RamifiedQuotientLogarithm.localPoint (baseChange ℚ_[3] P) : CyclotomicRamifiedField.Extension) =
      CyclotomicRamifiedField.linear (a : ℚ_[3]) (b : ℚ_[3]) := by
  have h := map_parameter_linear ℚ_[3] RamifiedQuotientLogarithm.place.toAlgHom P a b hP
  simpa only [AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe,
    RamifiedQuotientLogarithm.place_zeta, CyclotomicRamifiedField.linear,
    map_ratCast, eq_ratCast] using h

theorem split_coefficients_of_compact [Fact (p % 3 = 1)] (P : Points) (a b : ℚ)
    (hP : (parameterEquiv P : E) = algebraMap ℚ E a + algebraMap ℚ E b * zeta)
    (hc : baseChange ℚ_[p] P ∈ QuotientLocalHaar.splitCompactUnits p) :
    ‖(a : ℚ_[p])‖ ≤ 1 ∧ ‖(b : ℚ_[p])‖ ≤ 1 := by
  change QuotientLocalModels.splitEquiv p (baseChange ℚ_[p] P) ∈ SplitLocalModel.compactUnits p at hc
  rw [QuotientLocalModels.splitEquiv_apply] at hc
  have h₁ : ‖((SplitQuotientLogarithm.localPoint p (baseChange ℚ_[p] P)).1 : ℚ_[p])‖ ≤ 1 := hc.1.1
  have h₂ : ‖((SplitQuotientLogarithm.localPoint p (baseChange ℚ_[p] P)).2 : ℚ_[p])‖ ≤ 1 := hc.2.1
  have he := split_parameter_linear p P a b hP
  have he₁ := congrArg Prod.fst he
  have he₂ := congrArg Prod.snd he
  dsimp only at he₁ he₂
  rw [he₁] at h₁
  rw [he₂] at h₂
  exact split_coefficients_le_one p (by have := (Fact.out : p % 3 = 1); omega)
    _ _ _ (Classical.choose_spec (CyclotomicLocalRoots.field_root p Fact.out)) h₁ h₂

theorem inert_coefficients_of_compact [Fact (p % 3 = 2)] (P : Points) (a b : ℚ)
    (hP : (parameterEquiv P : E) = algebraMap ℚ E a + algebraMap ℚ E b * zeta)
    (hc : baseChange ℚ_[p] P ∈ QuotientLocalHaar.inertCompactUnits p) :
    ‖(a : ℚ_[p])‖ ≤ 1 ∧ ‖(b : ℚ_[p])‖ ≤ 1 := by
  change QuotientLocalModels.inertEquiv p (baseChange ℚ_[p] P) ∈ InertLocalModel.compactUnits p at hc
  rw [QuotientLocalModels.inertEquiv_apply] at hc
  have h := (CyclotomicInertField.mem_compactUnits p _).mp hc |>.1
  rwa [inert_parameter_linear p P a b hP, CyclotomicInertField.norm_linear, max_le_iff] at h

theorem ramified_coefficients_of_compact (P : Points) (a b : ℚ)
    (hP : (parameterEquiv P : E) = algebraMap ℚ E a + algebraMap ℚ E b * zeta)
    (hc : baseChange ℚ_[3] P ∈ QuotientLocalHaar.ramifiedCompactUnits) :
    ‖(a : ℚ_[3])‖ ≤ 1 ∧ ‖(b : ℚ_[3])‖ ≤ 1 := by
  change QuotientLocalModels.ramifiedEquiv (baseChange ℚ_[3] P) ∈ RamifiedLocalModel.compactUnits at hc
  rw [QuotientLocalModels.ramifiedEquiv_apply] at hc
  have h := (CyclotomicRamifiedField.mem_compactUnits _).mp hc |>.1
  rwa [ramified_parameter_linear P a b hP,
    CyclotomicRamifiedField.norm_linear_le_one_iff] at h

end Cubic.PoissonSummation.RationalLocalIntegers
