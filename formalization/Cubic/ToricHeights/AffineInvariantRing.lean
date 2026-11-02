import Cubic.ToricHeights.AffineIntegralModel
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic.FinCases

/-!
# The original integral invariant polynomials on the affine chart

The chart has independent coordinates `x=X/ε`, `y=Y/ε`, with `z=1-x-y`.
The cyclic generator sends `(x,y,z)` to `(z,x,y)`. We take its fixed ring
over `ℤ` first and then restrict its functions to the original quotient
torus. Thus the point definition tests every integral invariant polynomial,
without assuming generation by any small list of invariants or commutation
of invariants with restriction.
-/

noncomputable section

namespace Cubic.ToricHeights.AffineInvariantRing

open Cubic.QuadraticCorrespondence CyclotomicField CyclotomicTorusGalois
open DescendedCoefficients DescendedCyclicInvariant SplitLaurentInvariants
open MvPolynomial

abbrev ChartRing := MvPolynomial (Fin 2) ℤ

def thirdCoordinate : ChartRing := 1 - X 0 - X 1

def cycle : ChartRing →ₐ[ℤ] ChartRing :=
  aeval (fun i : Fin 2 => if i = 0 then thirdCoordinate else X 0)

@[simp] theorem cycle_X_zero : cycle (X 0) = thirdCoordinate := by simp [cycle]
@[simp] theorem cycle_X_one : cycle (X 1) = X 0 := by simp [cycle]
@[simp] theorem cycle_third : cycle thirdCoordinate = X 1 := by
  simp [thirdCoordinate]
  ring

theorem cycle_cube : cycle.comp (cycle.comp cycle) = AlgHom.id ℤ ChartRing := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp

def invariants : Subalgebra ℤ ChartRing := AlgHom.equalizer cycle (AlgHom.id ℤ _)

def restrict : ChartRing →ₐ[ℤ] CoverRing :=
  aeval (fun i : Fin 2 => if i = 0 then coverCoordinate 0 else coverCoordinate 1)

@[simp] theorem restrict_X_zero : restrict (X 0) = coverCoordinate 0 := by simp [restrict]
@[simp] theorem restrict_X_one : restrict (X 1) = coverCoordinate 1 := by simp [restrict]

@[simp] theorem restrict_third : restrict thirdCoordinate = coverCoordinate 2 := by
  have h := Cubic.OrbitParametrization.CyclicGroupAlgebra.trace_one CoverRing universalCover
  change coverCoordinate 0 + coverCoordinate 1 + coverCoordinate 2 = 1 at h
  simp only [thirdCoordinate, map_sub, map_one, restrict_X_zero, restrict_X_one]
  linear_combination -h

theorem restrict_cycle (f : ChartRing) :
    restrict (cycle f) = twist (SplitCoverFunctor.rootUnit zeta zeta_relation) (restrict f) := by
  have h : restrict.comp cycle =
      ((twist (SplitCoverFunctor.rootUnit zeta zeta_relation)).restrictScalars ℤ).comp restrict := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [coverCoordinate_twist]
    congr 1
  exact congrArg (fun g : ChartRing →ₐ[ℤ] CoverRing => g f) h

theorem restrict_conjugation (f : ChartRing) :
    SplitLaurentGalois.conjugate conjugation (restrict f) = restrict f := by
  have h : ((SplitLaurentGalois.conjugate conjugation).toAlgHom.restrictScalars ℤ).comp restrict =
      restrict := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [coverCoordinate_conjugation]
  exact congrArg (fun g : ChartRing →ₐ[ℤ] CoverRing => g f) h

/-- Restrict an integral invariant polynomial to the rational quotient torus. -/
def invariantRestriction : invariants →ₐ[ℤ] quotientFixedRing where
  toFun f := ⟨restrict f.val, restrict_conjugation f.val, by
    change twist (SplitCoverFunctor.rootUnit zeta zeta_relation) (restrict f.val) = restrict f.val
    rw [← restrict_cycle]
    exact congrArg restrict f.property⟩
  map_zero' := Subtype.ext (map_zero restrict)
  map_one' := Subtype.ext (map_one restrict)
  map_add' f g := Subtype.ext (map_add restrict f.val g.val)
  map_mul' f g := Subtype.ext (map_mul restrict f.val g.val)
  commutes' z := Subtype.ext (restrict.commutes z)

/-- All functions in the original integral invariant ring are required to be integer valued. -/
def IntegralPoint (P : quotientFixedRing →ₐ[ℚ] ℚ) : Prop :=
  ∀ f : invariants, ∃ z : ℤ, P (invariantRestriction f) = (z : ℚ)

theorem restrict_mem (f : ChartRing) : restrict f ∈ AffineIntegralModel.affineCoverFunctions := by
  have h : restrict.range ≤ AffineIntegralModel.affineCoverFunctions := by
    rw [restrict, ← Algebra.adjoin_range_eq_range_aeval]
    apply Algebra.adjoin_le
    rintro _ ⟨i, rfl⟩
    dsimp only
    split <;> apply AffineIntegralModel.coverCoordinate_mem
  exact h ⟨f, rfl⟩

theorem invariantRestriction_mem (f : invariants) :
    invariantRestriction f ∈ AffineIntegralModel.affineFunctions := restrict_mem f.val

def linearPolynomial : ChartRing := X 0 * X 1 + X 1 * thirdCoordinate + thirdCoordinate * X 0
def constantPolynomial : ChartRing := -(X 0 * X 1 * thirdCoordinate)

theorem linearPolynomial_fixed : linearPolynomial ∈ invariants := by
  change cycle linearPolynomial = linearPolynomial
  simp only [linearPolynomial, map_add, map_mul, cycle_X_zero, cycle_X_one, cycle_third]
  ring

theorem constantPolynomial_fixed : constantPolynomial ∈ invariants := by
  change cycle constantPolynomial = constantPolynomial
  simp only [constantPolynomial, map_neg, map_mul, cycle_X_zero, cycle_X_one, cycle_third]
  ring

theorem invariantRestriction_linear :
    invariantRestriction ⟨linearPolynomial, linearPolynomial_fixed⟩ = linearCoefficient := by
  apply Subtype.ext
  change restrict linearPolynomial = coverLinearCoefficient
  simp [linearPolynomial, coverLinearCoefficient, Cubic.OrbitParametrization.secondCoeff]

theorem invariantRestriction_constant :
    invariantRestriction ⟨constantPolynomial, constantPolynomial_fixed⟩ = constantCoefficient := by
  apply Subtype.ext
  change restrict constantPolynomial = coverConstantCoefficient
  simp [constantPolynomial, coverConstantCoefficient, Cubic.OrbitParametrization.constantCoeff]

theorem coefficients_of_integralPoint (P : quotientFixedRing →ₐ[ℚ] ℚ)
    (h : IntegralPoint P) :
    (∃ a : ℤ, P linearCoefficient = (a : ℚ)) ∧
      (∃ b : ℤ, P constantCoefficient = (b : ℚ)) := by
  constructor
  · simpa only [invariantRestriction_linear] using h ⟨linearPolynomial, linearPolynomial_fixed⟩
  · simpa only [invariantRestriction_constant] using h ⟨constantPolynomial, constantPolynomial_fixed⟩

end Cubic.ToricHeights.AffineInvariantRing
