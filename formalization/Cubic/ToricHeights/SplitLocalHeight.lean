import Cubic.ToricHeights.SplitLocalModel
import Cubic.ToricHeights.SupportFunction
import Cubic.PoissonSummation.LatticeCone
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Topology.Algebra.PontryaginDual

/-!
# Height and unramified spectral character in the split coordinate model

The height comes from the full cubic support function. The integral locus is the
valuation preimage of the enlarged-lattice cone, and the character uses
the paper's sign `p^(-π i t (n₁+n₂))`. The comparison with the original local
quotient is in `QuotientLocalModels`, `QuotientLocalIntegrality` and
`SplitQuotientLogarithm`.
-/

noncomputable section

namespace Cubic.ToricHeights.SplitLocalModel

open Cubic.OrbitParametrization.CocharacterLattice
open Cubic.PoissonSummation.LatticeCone

variable (p : ℕ) [Fact p.Prime]

def rayCoordinates (x : Points p) : ℝ × ℝ :=
  let n := coordinates (valuation p x).toAdd
  ((n.1 : ℝ), (n.2 : ℝ))

/-- Total ray degree, also outside the integral cone (where it can be negative). -/
def degree (x : Points p) : ℤ := (valuation p x).toAdd.1 + (valuation p x).toAdd.2

theorem rayCoordinates_sum (x : Points p) :
    (rayCoordinates p x).1 + (rayCoordinates p x).2 = (degree p x : ℝ) := by
  simp [rayCoordinates, coordinates, degree]
  ring

@[simp]
theorem degree_one : degree p 1 = 0 := by simp [degree]

theorem degree_mul (x y : Points p) : degree p (x * y) = degree p x + degree p y := by
  simp [degree, map_mul]
  ring

/-- The inverse local height before the integrality cutoff. -/
def inverseHeight (s₀ σ : ℂ) (x : Points p) : ℂ :=
  (p : ℂ) ^ supportFunction s₀ σ (rayCoordinates p x)

def integralLocus : Set (Points p) := {x | InCone (valuation p x).toAdd}

theorem measurable_integralLocus : MeasurableSet (integralLocus p) :=
  ((locallyConstant_valuation p) {n | InCone n.toAdd}).measurableSet

/-- The local component of the spectral character in these coordinates. -/
def character (t : ℝ) : PontryaginDual (Points p) where
  toFun x := Circle.exp (-Real.pi * t * Real.log p * (degree p x : ℝ))
  map_one' := by simp
  map_mul' x y := by rw [degree_mul, Int.cast_add, mul_add, Circle.exp_add]
  continuous_toFun := ((locallyConstant_valuation p).comp
    (fun n => Circle.exp (-Real.pi * t * Real.log p * ((n.toAdd.1 + n.toAdd.2 : ℤ) : ℝ)))).continuous

@[simp]
theorem character_zero : character p 0 = 1 := by
  apply DFunLike.ext
  intro x
  change Circle.exp (-Real.pi * 0 * Real.log p * (degree p x : ℝ)) = 1
  simp

/-- This character is unramified: it is trivial on the maximal compact. -/
theorem character_on_compactUnits (t : ℝ) (x : Points p) (hx : x ∈ compactUnits p) :
    character p t x = 1 := by
  have hv : valuation p x = 1 := by
    change x ∈ (valuation p).ker
    rwa [ker_valuation]
  have hd : degree p x = 0 := by simp [degree, hv]
  change Circle.exp (-Real.pi * t * Real.log p * (degree p x : ℝ)) = 1
  simp [hd]

/-- Check the character's sign against the paper's complex-power expression. -/
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

/-- On the integral cone the height is independent of `s₀`. -/
theorem inverseHeight_on_cone (s₀ σ : ℂ) (x : Points p)
    (hx : x ∈ integralLocus p) :
    inverseHeight p s₀ σ x = (p : ℂ) ^ (-σ * (degree p x : ℂ)) := by
  have hnonneg : 0 ≤ (rayCoordinates p x).1 ∧ 0 ≤ (rayCoordinates p x).2 := by
    dsimp [rayCoordinates]
    constructor
    · exact_mod_cast hx.1
    · exact_mod_cast hx.2
  unfold inverseHeight
  rw [supportFunction_on_integralCone s₀ σ hnonneg.1 hnonneg.2]
  have hsum : ((rayCoordinates p x).1 : ℂ) + ((rayCoordinates p x).2 : ℂ) =
      (degree p x : ℂ) := by exact_mod_cast rayCoordinates_sum p x
  rw [hsum]

end Cubic.ToricHeights.SplitLocalModel
