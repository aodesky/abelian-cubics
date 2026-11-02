import Cubic.QuadraticCorrespondence.CyclotomicField
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.NumberField.DedekindZeta

/-!
# The class-number-formula residue for `ℚ(√(-3))`

Specialize mathlib's ideal-counting Dedekind zeta residue, using the actual
third cyclotomic field. This is the arithmetic residue calculation in the
proof of `prop:leadingTerms`; comparison with an analytic continuation and
with `L(1,χ)` is established where the corresponding paper result is assembled.
-/

noncomputable section

namespace Cubic.PoissonSummation.QuadraticDedekindResidue

open Cubic.QuadraticCorrespondence.CyclotomicField
open NumberField NumberField.InfinitePlace NumberField.Units

theorem real_places : nrRealPlaces E = 0 :=
  IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero E (n := 3) (by decide)

theorem complex_places : nrComplexPlaces E = 1 := by
  simpa using IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two 3 E

theorem unit_rank : rank E = 0 := by
  simp [rank, card_eq_nrRealPlaces_add_nrComplexPlaces, real_places, complex_places]

theorem regulator_value : regulator E = 1 := by
  classical
  haveI : IsEmpty (Fin (rank E)) := by rw [unit_rank]; infer_instance
  haveI := (equivFinRank E).symm.isEmpty
  simp [regulator_eq_det']

theorem class_number : classNumber E = 1 :=
  classNumber_eq_one_iff.mpr (IsCyclotomicExtension.Rat.three_pid E)

theorem torsion_order : torsionOrder E = 6 := by
  simpa using IsCyclotomicExtension.Rat.torsionOrder_eq (K := E) (n := 3)

theorem discriminant : discr E = -3 := by
  simpa using IsCyclotomicExtension.Rat.discr_prime 3 E

theorem residue_value : dedekindZeta_residue E = Real.pi / (3 * Real.sqrt 3) := by
  rw [dedekindZeta_residue_def, real_places, complex_places, regulator_value,
    class_number, torsion_order, discriminant]
  norm_num
  ring

theorem residue_value_complex : (dedekindZeta_residue E : ℂ) =
    (Real.pi : ℂ) / (3 * (Real.sqrt 3 : ℂ)) := by
  rw [residue_value]
  push_cast
  rfl

/-- This is a limit of the genuine ideal-counting zeta series, not a renamed `ζ L`. -/
theorem residue_limit : Filter.Tendsto
    (fun s : ℝ => ((s - 1 : ℝ) : ℂ) * dedekindZeta E s)
    (nhdsWithin 1 (Set.Ioi 1))
    (nhds ((Real.pi : ℂ) / (3 * (Real.sqrt 3 : ℂ)))) := by
  simpa only [Complex.ofReal_sub, Complex.ofReal_one, residue_value_complex] using
    tendsto_sub_one_mul_dedekindZeta_nhdsGT E

end Cubic.PoissonSummation.QuadraticDedekindResidue
