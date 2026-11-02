import Cubic.BoxAsymptotic.IdealAngularData

/-! Independence of the generator for angular frequencies divisible by six.
This is the algebraic check needed when the primitive Hecke character is
unramified at three. -/

noncomputable section

namespace Cubic.BoxAsymptotic.HeckeGeneratorPhases

open Cubic.PoissonSummation.CyclotomicIntegerUnits
open Cubic.Counting.EisensteinNormCount
open Cubic.BoxAsymptotic.AngularSeriesData Cubic.BoxAsymptotic.AngularIdealData
open Cubic.BoxAsymptotic.AngularIdeals Cubic.BoxAsymptotic.EisensteinCoordinates
open Cubic.BoxAsymptotic.IdealAngularData
open CubicTargets.BoxAsymptotic

@[simp] theorem coordinates_zero : coordinates (0 : Integers) = 0 := by
  apply coord_injective
  rw [coord_coordinates]
  simp [coord]

@[simp] theorem coordinates_one : coordinates (1 : Integers) = (1, 0) := by
  apply coord_injective
  rw [coord_coordinates]
  simp [coord]

theorem coordinates_add (x y : Integers) : coordinates (x + y) = coordinates x + coordinates y := by
  apply coord_injective
  rw [coord_coordinates]
  have hc (p q : ℤ × ℤ) : coord (p + q) = coord p + coord q := by
    simp [coord]
    ring
  rw [hc, coord_coordinates, coord_coordinates]

def embedding : Integers →+* ℂ where
  toFun x := eis (coordinates x)
  map_zero' := by apply Complex.ext <;> simp [eis]
  map_one' := by apply Complex.ext <;> simp [eis]
  map_add' x y := by
    rw [coordinates_add]
    apply Complex.ext <;> simp [eis] <;> ring
  map_mul' x y := by rw [coordinates_mul, eis_mulE]

theorem embedding_injective : Function.Injective embedding := by
  intro x y h
  have hc := eis_injective h
  simpa using congrArg coord hc

theorem embedding_ne_zero {x : Integers} (hx : x ≠ 0) : embedding x ≠ 0 := by
  intro h
  exact hx (embedding_injective (h.trans (map_zero embedding).symm))

theorem unit_six (u : Integersˣ) : embedding (u : Integers) ^ 6 = 1 := by
  have h : (u : Integers) ^ 6 = 1 := by
    simpa using congrArg (fun v : Integersˣ => (v : Integers)) (unit_pow_six u)
  rw [← map_pow, h, map_one]

theorem norm_unit (u : Integersˣ) : ‖embedding (u : Integers)‖ = 1 := by
  apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num : (6 : ℕ) ≠ 0)).mp
  rw [← norm_pow, unit_six, norm_one]

theorem phase_unit {k : ℤ} (hk : 6 ∣ k) (u : Integersˣ) :
    phase k (embedding (u : Integers)) = 1 := by
  obtain ⟨j, rfl⟩ := hk
  rw [phase_eq_div _ (embedding_ne_zero u.ne_zero), norm_unit]
  simp only [Complex.ofReal_one, div_one, zpow_mul, zpow_ofNat, unit_six, one_zpow]

theorem phase_associated {k : ℤ} (hk : 6 ∣ k) {x y : Integers}
    (hx : x ≠ 0) (hxy : Associated x y) :
    phase k (embedding x) = phase k (embedding y) := by
  obtain ⟨u, rfl⟩ := hxy
  rw [map_mul, phase_mul k (embedding_ne_zero hx) (embedding_ne_zero u.ne_zero),
    phase_unit hk, mul_one]

theorem phase_span {k : ℤ} (hk : 6 ∣ k) {x : Integers} (hx : x ≠ 0) :
    generatorPhase k (Ideal.span {x}) = phase k (embedding x) := by
  have hI : Ideal.span {x} ≠ ⊥ := fun h => hx (Ideal.span_singleton_eq_bot.mp h)
  rw [generatorPhase_eq k hI]
  change phase k (embedding (chosenGenerator (Ideal.span {x}))) = _
  have hx' : chosenGenerator (Ideal.span {x}) ≠ 0 := by
    intro h
    have hs := span_chosen (Ideal.span {x})
    rw [h, Ideal.span_singleton_eq_bot.mpr rfl] at hs
    exact hI hs.symm
  exact phase_associated hk hx' (Ideal.span_singleton_eq_span_singleton.mp (span_chosen _))

theorem chosen_ne_zero {I : Ideal Integers} (hI : I ≠ ⊥) : chosenGenerator I ≠ 0 := by
  intro h
  have hs := span_chosen I
  rw [h, Ideal.span_singleton_eq_bot.mpr rfl] at hs
  exact hI hs.symm

theorem generatorPhase_mul {k : ℤ} (hk : 6 ∣ k) (I J : Ideal Integers) :
    generatorPhase k (I * J) = generatorPhase k I * generatorPhase k J := by
  classical
  by_cases hI : I = ⊥
  · simp [hI, generatorPhase]
  by_cases hJ : J = ⊥
  · simp [hJ, generatorPhase]
  have hspan : I * J = Ideal.span {chosenGenerator I * chosenGenerator J} := by
    rw [← Ideal.span_singleton_mul_span_singleton, span_chosen, span_chosen]
  rw [hspan, phase_span hk (mul_ne_zero (chosen_ne_zero hI) (chosen_ne_zero hJ)),
    map_mul, phase_mul k (embedding_ne_zero (chosen_ne_zero hI))
      (embedding_ne_zero (chosen_ne_zero hJ)),
    generatorPhase_eq k hI, generatorPhase_eq k hJ]
  rfl

theorem generatorPhase_one {k : ℤ} (hk : 6 ∣ k) : generatorPhase k 1 = 1 := by
  have h := phase_span hk (one_ne_zero : (1 : Integers) ≠ 0)
  simpa [phase, character] using h

end Cubic.BoxAsymptotic.HeckeGeneratorPhases
