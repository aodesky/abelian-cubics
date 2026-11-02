import Cubic.ToricHeights.InertLocalValuation
import Cubic.ToricHeights.SupportFunction
import Cubic.PoissonSummation.LatticeCone
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Topology.Algebra.PontryaginDual

/-!
# Height and spectral character on the inert local field

The cutoff is integrality in the extension norm. Its equivalence with
the invariant lattice cone is proved using the normalized valuation. The
height uses the full cubic support function; the spectral character has the
paper's sign and degree `2ν`. The comparison with the original local quotient
is in `QuotientLocalModels`, `QuotientLocalIntegrality` and `InertQuotientLogarithm`.
-/

noncomputable section

namespace Cubic.ToricHeights.InertLocalModel

open Cubic.OrbitParametrization.CocharacterLattice
open Cubic.PoissonSummation.LatticeCone
open Cubic.QuadraticCorrespondence.CyclotomicInertField (Extension)

variable (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 2)]

def rayCoordinates (x : Points p) : ℝ × ℝ :=
  let n := coordinates (valuation p x).toAdd
  ((n.1 : ℝ), (n.2 : ℝ))

def degree (x : Points p) : ℤ := (valuation p x).toAdd.val.1 + (valuation p x).toAdd.val.2

theorem degree_eq_two_ord (x : Points p) : degree p x = 2 * ord p x := by
  simp [degree, valuation, integerValuation, invariantCoordinate]
  ring

theorem rayCoordinates_sum (x : Points p) :
    (rayCoordinates p x).1 + (rayCoordinates p x).2 = (degree p x : ℝ) := by
  simp [rayCoordinates, coordinates, degree]
  ring

@[simp]
theorem degree_one : degree p 1 = 0 := by simp [degree]

theorem degree_mul (x y : Points p) : degree p (x * y) = degree p x + degree p y := by
  simp [degree, map_mul]
  ring

/-- The full support-function height, before applying the integrality cutoff. -/
def inverseHeight (s₀ σ : ℂ) (x : Points p) : ℂ :=
  (p : ℂ) ^ supportFunction s₀ σ (rayCoordinates p x)

/-- Integrality in the quadratic local field. -/
def integralLocus : Set (Points p) := {x | ‖(x : Extension p)‖ ≤ 1}

theorem measurable_integralLocus : MeasurableSet (integralLocus p) :=
  (isClosed_le (continuous_norm.comp Units.continuous_val) continuous_const).measurableSet

/-- Integrality is exactly the cone condition for the invariant cocharacter. -/
theorem mem_integralLocus_iff_cone (x : Points p) :
    x ∈ integralLocus p ↔ InCone (valuation p x).toAdd.val := by
  change ‖(x : Extension p)‖ ≤ 1 ↔ _
  rw [norm_le_one_iff_ord_nonneg]
  simp only [InCone, valuation_coordinates, and_self]
  constructor <;> intro h <;> exact_mod_cast h

/-- The local unramified character with the paper's inverse-Fourier convention. -/
def character (t : ℝ) : PontryaginDual (Points p) where
  toFun x := Circle.exp (-Real.pi * t * Real.log p * (degree p x : ℝ))
  map_one' := by simp
  map_mul' x y := by rw [degree_mul, Int.cast_add, mul_add, Circle.exp_add]
  continuous_toFun := ((locallyConstant_valuation p).comp
    (fun n => Circle.exp (-Real.pi * t * Real.log p *
      ((n.toAdd.val.1 + n.toAdd.val.2 : ℤ) : ℝ)))).continuous

@[simp]
theorem character_zero : character p 0 = 1 := by
  apply DFunLike.ext
  intro x
  change Circle.exp (-Real.pi * 0 * Real.log p * (degree p x : ℝ)) = 1
  simp

theorem character_on_compactUnits (t : ℝ) (x : Points p) (hx : x ∈ compactUnits p) :
    character p t x = 1 := by
  have hv : valuation p x = 1 := by
    change x ∈ (valuation p).ker
    rwa [ker_valuation]
  have hd : degree p x = 0 := by simp [degree, hv]
  change Circle.exp (-Real.pi * t * Real.log p * (degree p x : ℝ)) = 1
  simp [hd]

theorem character_eq_cpow (t : ℝ) (x : Points p) :
    ((character p t x : Circle) : ℂ) =
      (p : ℂ) ^ (-Real.pi * Complex.I * (t : ℂ) * (degree p x : ℂ)) := by
  have hp : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  change Complex.exp (((-Real.pi * t * Real.log p * (degree p x : ℝ)) : ℝ) * Complex.I) = _
  rw [Complex.cpow_def_of_ne_zero hp]
  have hlog : Complex.log (p : ℂ) = (Real.log (p : ℝ) : ℂ) :=
    (Complex.ofReal_log (Nat.cast_nonneg p)).symm
  rw [hlog]
  push_cast
  congr 1
  ring

/-- On the integral cone, the inverse height has exponent `-2σν` and is
independent of `s₀`; the degree equality is recorded separately above. -/
theorem inverseHeight_on_cone (s₀ σ : ℂ) (x : Points p) (hx : x ∈ integralLocus p) :
    inverseHeight p s₀ σ x = (p : ℂ) ^ (-σ * (degree p x : ℂ)) := by
  have hc := (mem_integralLocus_iff_cone p x).mp hx
  have hnonneg : 0 ≤ (rayCoordinates p x).1 ∧ 0 ≤ (rayCoordinates p x).2 := by
    dsimp [rayCoordinates]
    constructor
    · exact_mod_cast hc.1
    · exact_mod_cast hc.2
  unfold inverseHeight
  rw [supportFunction_on_integralCone s₀ σ hnonneg.1 hnonneg.2]
  have hsum : ((rayCoordinates p x).1 : ℂ) + ((rayCoordinates p x).2 : ℂ) =
      (degree p x : ℂ) := by exact_mod_cast rayCoordinates_sum p x
  rw [hsum]

end Cubic.ToricHeights.InertLocalModel
