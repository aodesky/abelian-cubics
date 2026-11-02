import Cubic.ToricHeights.AffineInvariantRing

/-!
# The dehomogenized invariants `e₂, e₃, δ` on the trace-one chart

On the chart `ℤ[X/ε, Y/ε] = ChartRing` with `x = X/ε`, `y = Y/ε` and
`z = Z/ε = 1 - x - y` (`AffineInvariantRing.thirdCoordinate`), the paper's
dehomogenized invariants are
`e₂ = (XY+YZ+ZX)/ε² = xy+yz+zx`, `e₃ = XYZ/ε³ = xyz` and
`δ = (X²Y+Y²Z+Z²X)/ε³ = x²y+y²z+z²x`. The `C₃`-action is
`AffineInvariantRing.cycle`, `(x,y,z) ↦ (z,x,y)`.
-/

noncomputable section

namespace Cubic.ToricHeights.AffineChartInvariants

open MvPolynomial AffineInvariantRing

/-- `e₂ = (XY+YZ+ZX)/ε²` on the chart (this is `linearPolynomial`). -/
abbrev e2 : ChartRing := linearPolynomial

/-- `e₃ = XYZ/ε³` on the chart. -/
def e3 : ChartRing := X 0 * X 1 * thirdCoordinate

/-- `δ = (X²Y+Y²Z+Z²X)/ε³` on the chart. -/
def delta : ChartRing := X 0 ^ 2 * X 1 + X 1 ^ 2 * thirdCoordinate + thirdCoordinate ^ 2 * X 0

theorem e2_mem : e2 ∈ invariants := linearPolynomial_fixed

theorem e3_mem : e3 ∈ invariants := by
  change cycle e3 = e3
  simp only [e3, map_mul, cycle_X_zero, cycle_X_one, cycle_third]
  ring

theorem delta_mem : delta ∈ invariants := by
  change cycle delta = delta
  simp only [delta, map_mul, map_add, map_pow, cycle_X_zero, cycle_X_one, cycle_third]
  ring

/-- Rational points of `S ∖ D₀`. Since `𝒪(S_ℤ ∖ D₀) = ℤ[X/ε,Y/ε]^{C₃}`
(= `AffineInvariantRing.invariants`), a rational point of `S ∖ D₀` (the generic fibre of
`S_ℤ ∖ D₀ = Spec ℤ[X/ε,Y/ε]^{C₃}`) is a ring homomorphism `ℤ[X/ε,Y/ε]^{C₃} → ℚ`; these are
the same as `ℚ`-algebra maps `ℚ ⊗ ℤ[X/ε,Y/ε]^{C₃} → ℚ`. This includes points with
vanishing discriminant, not only points of the torus `T`. -/
abbrev RationalPoint := invariants →+* ℚ

/-- The paper's `D₀`-integrality: every regular function in `𝒪(S_ℤ ∖ D₀)` is `ℤ`-valued
at `P`. -/
def IsD0Integral (P : RationalPoint) : Prop :=
  ∀ f : invariants, ∃ z : ℤ, P f = (z : ℚ)

end Cubic.ToricHeights.AffineChartInvariants
