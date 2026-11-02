import Cubic.ToricHeights.InertLocalModel
import Cubic.QuadraticCorrespondence.CyclotomicInertNorm
import Cubic.OrbitParametrization.PadicMultiplicative
import Cubic.OrbitParametrization.CocharacterLattice

/-!
# The normalized valuation at an inert place

The proved norm formula gives an integer `ν(x)` with `‖x‖ = p^(-ν(x))`.
This defines a surjective valuation homomorphism, sends `p` to one, and has
the maximal compact as its kernel. In the paper's cocharacter lattice
its value is `ν(x)(v₁+v₂)`, including negative valuations.
-/

noncomputable section

namespace Cubic.ToricHeights.InertLocalModel

open Cubic.QuadraticCorrespondence.CyclotomicInertField
open Cubic.OrbitParametrization.CocharacterLattice
open Cubic.OrbitParametrization

variable (p : ℕ) [Fact p.Prime]

private theorem prime_one_lt : 1 < (p : ℝ) := by
  exact_mod_cast (Fact.out : p.Prime).one_lt

private theorem norm_power_injective : Function.Injective (fun n : ℤ => (p : ℝ) ^ (-n)) :=
  (zpow_right_injective₀ (zero_lt_one.trans (prime_one_lt p)) (prime_one_lt p).ne').comp
    neg_injective

variable [Fact (p % 3 = 2)]

private theorem exists_ord (x : Points p) : ∃ n : ℤ, ‖(x : Extension p)‖ = (p : ℝ) ^ (-n) := by
  obtain ⟨a, ha⟩ := exists_norm_eq_padic p (x : Extension p)
  have ha0 : a ≠ 0 := by
    intro h
    simp [h] at ha
  exact ⟨Padic.valuation a, ha.trans (Padic.norm_eq_zpow_neg_valuation ha0)⟩

/-- The integral valuation determined by the extension of the p-adic norm. -/
def ord (x : Points p) : ℤ := Classical.choose (exists_ord p x)

theorem norm_eq_zpow_ord (x : Points p) : ‖(x : Extension p)‖ = (p : ℝ) ^ (-ord p x) :=
  Classical.choose_spec (exists_ord p x)

theorem ord_eq_of_norm_eq (x : Points p) {n : ℤ}
    (h : ‖(x : Extension p)‖ = (p : ℝ) ^ (-n)) : ord p x = n :=
  norm_power_injective p ((norm_eq_zpow_ord p x).symm.trans h)

@[simp]
theorem ord_one : ord p 1 = 0 := ord_eq_of_norm_eq p 1 (by simp)

theorem ord_mul (x y : Points p) : ord p (x * y) = ord p x + ord p y := by
  apply ord_eq_of_norm_eq
  rw [Units.val_mul, norm_mul, norm_eq_zpow_ord, norm_eq_zpow_ord, neg_add,
    zpow_add₀ (ne_of_gt (zero_lt_one.trans (prime_one_lt p)))]

/-- The usual integer-valued local valuation, written multiplicatively on its target. -/
def integerValuation : Points p →* Multiplicative ℤ where
  toFun x := Multiplicative.ofAdd (ord p x)
  map_one' := by simp
  map_mul' x y := congrArg Multiplicative.ofAdd (ord_mul p x y)

/-- The extension is unramified: the valuation restricts to the base-field valuation. -/
theorem ord_scalarUnits (x : ℚ_[p]ˣ) :
    ord p (Units.map (algebraMap ℚ_[p] (Extension p)).toMonoidHom x) =
      Padic.valuation (x : ℚ_[p]) := by
  apply ord_eq_of_norm_eq
  change ‖algebraMap ℚ_[p] (Extension p) (x : ℚ_[p])‖ = _
  rw [Cubic.QuadraticCorrespondence.CyclotomicInertField.norm_algebraMap]
  exact Padic.norm_eq_zpow_neg_valuation x.ne_zero

/-- The rational prime is a uniformizer in this quadratic local field. -/
def uniformizer : Points p :=
  Units.map (algebraMap ℚ_[p] (Extension p)).toMonoidHom (PadicMultiplicative.uniformizer p)

@[simp]
theorem ord_uniformizer : ord p (uniformizer p) = 1 := by
  rw [uniformizer, ord_scalarUnits]
  simp [PadicMultiplicative.uniformizer]

@[simp]
theorem integerValuation_uniformizer :
    integerValuation p (uniformizer p) = Multiplicative.ofAdd 1 := by
  simp [integerValuation]

theorem integerValuation_surjective : Function.Surjective (integerValuation p) := by
  intro n
  refine ⟨uniformizer p ^ n.toAdd, ?_⟩
  rw [map_zpow, integerValuation_uniformizer]
  rw [← ofAdd_zsmul]
  simp

theorem ord_eq_zero_iff_norm_one (x : Points p) : ord p x = 0 ↔ ‖(x : Extension p)‖ = 1 := by
  constructor
  · intro h
    simp [norm_eq_zpow_ord p x, h]
  · intro h
    apply ord_eq_of_norm_eq
    simpa using h

theorem norm_le_one_iff_ord_nonneg (x : Points p) : ‖(x : Extension p)‖ ≤ 1 ↔ 0 ≤ ord p x := by
  rw [norm_eq_zpow_ord, ← zpow_zero (p : ℝ), zpow_le_zpow_iff_right₀ (prime_one_lt p)]
  omega

theorem ker_integerValuation : (integerValuation p).ker = compactUnits p := by
  ext x
  change ord p x = 0 ↔ x ∈ compactUnits p
  rw [ord_eq_zero_iff_norm_one, mem_compactUnits_iff_norm_one]

/-- The valuation in the paper's full invariant cocharacter lattice. -/
def valuation : Points p →* Multiplicative invariantLattice :=
  invariantCoordinate.toMultiplicative.toMonoidHom.comp (integerValuation p)

theorem valuation_surjective : Function.Surjective (valuation p) :=
  invariantCoordinate.toMultiplicative.surjective.comp (integerValuation_surjective p)

theorem ker_valuation : (valuation p).ker = compactUnits p := by
  ext x
  change invariantCoordinate (ord p x) = 0 ↔ x ∈ compactUnits p
  rw [map_eq_zero_iff invariantCoordinate invariantCoordinate.injective,
    ord_eq_zero_iff_norm_one, mem_compactUnits_iff_norm_one]

theorem valuation_coordinates (x : Points p) :
    coordinates (valuation p x).toAdd = ((ord p x : ℚ), (ord p x : ℚ)) :=
  coordinates_invariantCoordinate _

/-- Open valuation fibers give the measurability needed for integration as a lattice sum. -/
theorem locallyConstant_valuation : IsLocallyConstant (valuation p) := by
  apply IsLocallyConstant.iff_isOpen_fiber_apply.mpr
  intro g
  have hfiber : valuation p ⁻¹' {valuation p g} =
      (fun x => g⁻¹ * x) ⁻¹' ((valuation p).ker : Set (Points p)) := by
    ext x
    change valuation p x = valuation p g ↔ valuation p (g⁻¹ * x) = 1
    rw [map_mul, map_inv, inv_mul_eq_one]
    exact eq_comm
  rw [hfiber, ker_valuation]
  exact (isOpen_compactUnits p).preimage (continuous_const.mul continuous_id)

end Cubic.ToricHeights.InertLocalModel
