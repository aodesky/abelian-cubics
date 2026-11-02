import Cubic.BoxAsymptotic.HeckeConductor
import Cubic.BoxAsymptotic.HeckeSeriesConvergence
import Cubic.PoissonSummation.QuadraticDedekindResidue
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-! Arithmetic hypotheses and analytic conclusions of the imaginary-quadratic
Hecke theorem. The residue ring is an actual finite quotient, and the ideal
character is specified on principal ideals, not by its proposed L-function.
This file contains no assumed theorem.
-/

noncomputable section

namespace Cubic.BoxAsymptotic.PrimitiveHeckeData

open Cubic.PoissonSummation.CyclotomicIntegerUnits
open Cubic.QuadraticCorrespondence.CyclotomicField
open Cubic.BoxAsymptotic.AngularSeriesData Cubic.BoxAsymptotic.HeckeGeneratorPhases
open Cubic.BoxAsymptotic.HeckeConductor

/-- In the class-number-one field, specifying every nonzero principal ideal
specifies the whole ideal character. Nonunits modulo the conductor give zero. -/
structure PrincipalFormula {R : Type} [CommRing R]
    (red : Integers →+* R) (χ : Rˣ →* ℂ) (k : ℤ) (ψ : Ideal Integers →*₀ ℂ) : Prop where
  at_unit : ∀ x : Integers, x ≠ 0 → ∀ u : Rˣ, (u : R) = red x →
    ψ (Ideal.span {x}) = χ u * phase k (embedding x)
  at_nonunit : ∀ x : Integers, x ≠ 0 → ¬ IsUnit (red x) → ψ (Ideal.span {x}) = 0

/-- All applicability conditions for a primitive finite-order angular Hecke
character over the fixed, genuine imaginary-quadratic field `E`. -/
structure ArithmeticData {R : Type} [CommRing R] [Fintype R]
    (red : Integers →+* R) (χ : Rˣ →* ℂ) (k : ℤ) (ψ : Ideal Integers →*₀ ℂ) : Prop where
  surjective : Function.Surjective red
  kernel_nonzero : RingHom.ker red ≠ ⊥
  unitary : ∀ u, ‖χ u‖ = 1
  primitive : Primitive χ
  principal : PrincipalFormula red χ k ψ

/-- The norm of the conductor is the cardinality of the actual residue ring. -/
def scale (R : Type) [Fintype R] : ℝ :=
  Real.sqrt ((NumberField.discr E).natAbs * (Fintype.card R : ℝ)) / (2 * Real.pi)

def completedFactor (Q : ℝ) (k : ℤ) (s : ℂ) : ℂ :=
  (Q : ℂ) ^ s * Complex.Gamma (s + (k.natAbs : ℂ) / 2)

def PolynomialVerticalGrowth (L : ℂ → ℂ) : Prop :=
  ∀ a b : ℝ, a ≤ b → ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ,
    ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖L s‖ ≤ C * (1 + |s.im|) ^ N

/-- The completion is a separate entire function. Its Gamma-product formula
is asserted in the pole-free right half-plane, so totalized Gamma values at
negative integers cannot create a false global equality. -/
structure AnalyticData (ψ : Ideal Integers →*₀ ℂ) (Q : ℝ) (k : ℤ)
    (L Λ : ℂ → ℂ) (ε : ℂ) : Prop where
  entire : Differentiable ℂ L
  completed_entire : Differentiable ℂ Λ
  series_eq : ∀ s : ℂ, 1 < s.re → L s = LSeries (HeckeSeriesConvergence.coefficient ψ) s
  completion_eq : ∀ s : ℂ, 0 < s.re → Λ s = completedFactor Q k s * L s
  root_number : ‖ε‖ = 1
  functional_equation : ∀ s : ℂ, Λ s = ε * star (Λ (1 - star s))
  growth : PolynomialVerticalGrowth L

end Cubic.BoxAsymptotic.PrimitiveHeckeData
