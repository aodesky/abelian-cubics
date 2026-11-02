import Cubic.BoxAsymptotic.HeckeGeneratorPhases

/-! The finite character attached to the actual primary-generator character.
The reduction group consists of the units of `F₃[ε]/(ε²)` and is identified with
the six global units. `HeckeModulus` checks that its ring is `O/3O`.
Its inverse angular character supplies the unit consistency
condition in Iwaniec--Kowalski, §3.8, (3.80).
-/

noncomputable section

namespace Cubic.BoxAsymptotic.HeckeFiniteCharacter

open Cubic.PoissonSummation.CyclotomicIntegerUnits
open Cubic.BoxAsymptotic.AngularSeriesData Cubic.BoxAsymptotic.AngularIdealData
open Cubic.BoxAsymptotic.AngularIdeals Cubic.BoxAsymptotic.PrimaryGenerator
open Cubic.BoxAsymptotic.HeckeGeneratorPhases

abbrev ResidueRing := Cubic.QuadraticCorrespondence.CyclotomicRamifiedReduction.ResidueRing

def unitPhase (k : ℤ) : Integersˣ →* ℂ where
  toFun u := phase k (embedding (u : Integers))
  map_one' := by simp [phase, character]
  map_mul' u v := by
    rw [Units.val_mul, map_mul]
    exact phase_mul k (embedding_ne_zero u.ne_zero) (embedding_ne_zero v.ne_zero)

def finiteCharacter (k : ℤ) : ResidueRingˣ →* ℂ :=
  (unitPhase (-k)).comp residueUnitsEquiv.symm.toMonoidHom

theorem finiteCharacter_unit (k : ℤ) (u : Integersˣ) :
    finiteCharacter k (reductionUnits u) = phase (-k) (embedding (u : Integers)) := by
  change unitPhase (-k) (residueUnitsEquiv.symm (residueUnitsEquiv u)) = _
  rw [residueUnitsEquiv.symm_apply_apply]
  rfl

theorem norm_finiteCharacter (k : ℤ) (v : ResidueRingˣ) : ‖finiteCharacter k v‖ = 1 :=
  norm_phase _ _

theorem unit_consistency (k : ℤ) (u : Integersˣ) :
    finiteCharacter k (reductionUnits u) * phase k (embedding (u : Integers)) = 1 := by
  rw [finiteCharacter_unit, phase_eq_div _ (embedding_ne_zero u.ne_zero),
    phase_eq_div _ (embedding_ne_zero u.ne_zero), norm_unit]
  simp only [Complex.ofReal_one, div_one, zpow_neg]
  exact inv_mul_cancel₀ (zpow_ne_zero _ (embedding_ne_zero u.ne_zero))

theorem unramified_finiteCharacter {k : ℤ} (hk : 6 ∣ k) : finiteCharacter k = 1 := by
  ext v
  change phase (-k) (embedding ((residueUnitsEquiv.symm v : Integersˣ) : Integers)) = 1
  exact phase_unit (dvd_neg.mpr hk) _

theorem psi_one (k : ℤ) : psi k 1 = 1 := by
  have hg : generator (1 : Ideal Integers) = 1 :=
    generator_eq (by norm_num) (by simp [IsPrimary]) (by simp)
  rw [psi, if_neg (by norm_num : ¬ 3 ∣ Ideal.absNorm (1 : Ideal Integers)), hg]
  change phase k (embedding 1) = 1
  simp [phase, character]

def psiHom (k : ℤ) : Ideal Integers →*₀ ℂ where
  toFun := psi k
  map_zero' := by simp [psi]
  map_one' := psi_one k
  map_mul' := psi_mul k

theorem principal_primary (k : ℤ) {x : Integers} (hx : IsPrimary x)
    (h3 : ¬ 3 ∣ Ideal.absNorm (Ideal.span {x})) :
    psi k (Ideal.span {x}) = phase k (embedding x) := by
  rw [psi, if_neg h3, generator_eq h3 hx rfl]
  rfl

/-- Any lift of the residue unit can be used in the principal-ideal formula.
This avoids making a second, unrelated choice of primary generator. -/
theorem principal_formula (k : ℤ) {x : Integers} (hx : x ≠ 0)
    (h3 : ¬ 3 ∣ Ideal.absNorm (Ideal.span {x}))
    (u : Integersˣ) (hu : reduction (u : Integers) = reduction x) :
    psi k (Ideal.span {x}) =
      finiteCharacter k (reductionUnits u) * phase k (embedding x) := by
  have hprimary : IsPrimary (x * (u⁻¹ : Integersˣ)) := by
    change reduction (x * (u⁻¹ : Integersˣ)) = 1
    rw [map_mul, ← hu, ← map_mul]
    simp
  have hspan : Ideal.span {x * (u⁻¹ : Integersˣ)} = Ideal.span {x} :=
    Ideal.span_singleton_mul_right_unit (u⁻¹).isUnit x
  have hg := generator_eq h3 hprimary hspan
  rw [psi, if_neg h3, hg, finiteCharacter_unit]
  change phase k (embedding (x * (u⁻¹ : Integersˣ))) = _
  rw [map_mul, phase_mul k (embedding_ne_zero hx) (embedding_ne_zero (u⁻¹).ne_zero)]
  have hunit : phase k (embedding ((u⁻¹ : Integersˣ) : Integers)) =
      phase (-k) (embedding (u : Integers)) := by
    rw [phase_eq_div _ (embedding_ne_zero (u⁻¹).ne_zero),
      phase_eq_div _ (embedding_ne_zero u.ne_zero), norm_unit, norm_unit]
    simp only [Complex.ofReal_one, div_one, zpow_neg]
    have hi : embedding ((u⁻¹ : Integersˣ) : Integers) = (embedding (u : Integers))⁻¹ := by
      exact map_units_inv embedding u
    rw [hi, inv_zpow]
  rw [hunit, mul_comm]

end Cubic.BoxAsymptotic.HeckeFiniteCharacter
