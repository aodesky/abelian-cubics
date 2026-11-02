import Cubic.BoxAsymptotic.HeckeModulus
import Cubic.BoxAsymptotic.AngularUnitSums

/-! Primitivity of the finite character for frequencies not divisible by three.
Together with its triviality for multiples of six, this verifies the conductor
alternatives used in the positive-even-frequency moment argument.
-/

noncomputable section

namespace Cubic.BoxAsymptotic.HeckeConductor

open Cubic.PoissonSummation.CyclotomicIntegerUnits
open Cubic.BoxAsymptotic.HeckeFiniteCharacter Cubic.BoxAsymptotic.HeckeGeneratorPhases
open Cubic.BoxAsymptotic.AngularSeriesData Cubic.BoxAsymptotic.AngularIdealData
open Cubic.Counting.EisensteinNormCount
open Cubic.QuadraticCorrespondence
open scoped DualNumber

def quotientUnits {R : Type*} [CommRing R] (J : Ideal R) : Rˣ →* (R ⧸ J)ˣ :=
  Units.map (Ideal.Quotient.mk J).toMonoidHom

/-- A finite character is primitive if it does not factor through a nontrivial
quotient of the residue ring. For `O/m`, these are precisely the smaller moduli
dividing `m`, in the convention of Iwaniec--Kowalski, §3.8. -/
def Primitive {R : Type*} [CommRing R] (χ : Rˣ →* ℂ) : Prop :=
  ∀ J : Ideal R, ∀ ξ : (R ⧸ J)ˣ →* ℂ,
    χ = ξ.comp (quotientUnits J) → J = ⊥

theorem epsilon_mem {J : Ideal ResidueRing} (hJ : J ≠ ⊥) : (ε : ResidueRing) ∈ J := by
  obtain ⟨x, hx, hx0⟩ := J.ne_bot_iff.mp hJ
  by_cases hf : x.fst = 0
  · have hs : x.snd ≠ 0 := by
      intro hs
      apply hx0
      apply TrivSqZeroExt.ext <;> assumption
    have he : (TrivSqZeroExt.inl (x.snd⁻¹) : ResidueRing) * x = ε := by
      apply TrivSqZeroExt.ext <;> simp [hf, inv_mul_cancel₀ hs]
    rw [← he]
    exact J.mul_mem_left _ hx
  · have hu : IsUnit x := TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (isUnit_iff_ne_zero.mpr hf)
    rw [J.eq_top_of_isUnit_mem hx hu]
    trivial

theorem zeta_quotient_unit {J : Ideal ResidueRing} (hJ : J ≠ ⊥) :
    quotientUnits J (reductionUnits zetaUnit) = 1 := by
  apply Units.ext
  change Ideal.Quotient.mk J (reduction (zetaUnit : Integers)) = 1
  rw [coe_zetaUnit, reduction_zeta]
  change Ideal.Quotient.mk J CyclotomicRamifiedReduction.residueZeta = Ideal.Quotient.mk J 1
  apply Ideal.Quotient.eq.mpr
  simpa [CyclotomicRamifiedReduction.residueZeta] using epsilon_mem hJ

theorem embedding_zeta : embedding zetaInteger = AngularUnitSums.zeta := by
  have he : coord (0, 1) = zetaInteger := by simp [coord]
  change CubicTargets.BoxAsymptotic.eis (coordinates zetaInteger) = _
  rw [← he, coordinates_coord]
  rfl

theorem zeta_zpow_ne_one {k : ℤ} (hk : ¬ 3 ∣ k) : AngularUnitSums.zeta ^ k ≠ 1 := by
  intro h
  have hs := AngularUnitSums.zeta_sum k
  rw [h, if_neg hk] at hs
  norm_num at hs

theorem finiteCharacter_zeta (k : ℤ) :
    finiteCharacter k (reductionUnits zetaUnit) = AngularUnitSums.zeta ^ (-k) := by
  rw [finiteCharacter_unit, coe_zetaUnit, embedding_zeta,
    phase_eq_div _ AngularUnitSums.zeta_ne_zero, AngularUnitSums.norm_zeta]
  simp

theorem finiteCharacter_primitive {k : ℤ} (hk : ¬ 3 ∣ k) : Primitive (finiteCharacter k) := by
  intro J ξ hξ
  by_contra hJ
  have he := congrArg (fun χ : ResidueRingˣ →* ℂ => χ (reductionUnits zetaUnit)) hξ
  dsimp only at he
  rw [finiteCharacter_zeta, MonoidHom.comp_apply, zeta_quotient_unit hJ, map_one] at he
  exact zeta_zpow_ne_one (fun h => hk (dvd_neg.mp h)) he

theorem even_conductor_alternatives {k : ℤ} (hk : Even k) :
    (6 ∣ k ∧ finiteCharacter k = 1) ∨ (¬ 6 ∣ k ∧ Primitive (finiteCharacter k)) := by
  by_cases h6 : 6 ∣ k
  · exact Or.inl ⟨h6, unramified_finiteCharacter h6⟩
  · apply Or.inr
    refine ⟨h6, finiteCharacter_primitive ?_⟩
    have h2 : 2 ∣ k := even_iff_two_dvd.mp hk
    omega

end Cubic.BoxAsymptotic.HeckeConductor
