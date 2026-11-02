import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Ring

/-!
# Coordinates of a split trace-one cubic

Basic definitions for the paper's orbit parametrization. A split algebra is represented
by `Fin 3 → ℚ`; its three cyclic conjugates are the rows of `conjugates`.
Normality means linear independence of these vectors over `ℚ`.

The conjugate evaluation matrix and the group-algebra multiplication matrix
have opposite determinants.
-/

namespace Cubic.OrbitParametrization

/-- The cyclic conjugates of `(α, β, γ)` in the split algebra. -/
def conjugates {R : Type*} (α β γ : R) : Matrix (Fin 3) (Fin 3) R :=
  !![α, β, γ; β, γ, α; γ, α, β]

/-- Multiplication by `α + βσ + γσ²` in the ordered basis `(1, σ, σ²)`.
Its determinant is the paper's `Δ`. -/
def groupAlgebraMulMatrix {R : Type*} (α β γ : R) : Matrix (Fin 3) (Fin 3) R :=
  !![α, γ, β; β, α, γ; γ, β, α]

/-- Normality in the split rational algebra, as in the paper. -/
def IsNormal (α β γ : ℚ) : Prop :=
  LinearIndependent ℚ (conjugates α β γ)

/-- The second elementary symmetric function, hence the linear coefficient. -/
def secondCoeff {R : Type*} [CommRing R] (α β γ : R) : R :=
  α * β + β * γ + γ * α

/-- The constant coefficient of the monic polynomial with these three roots. -/
def constantCoeff {R : Type*} [CommRing R] (α β γ : R) : R :=
  -(α * β * γ)

/-- Evaluation of the cubic with trace one and coefficients `a`, `b`. -/
def traceOneCubic {R : Type*} [CommRing R] (a b t : R) : R :=
  t ^ 3 - t ^ 2 + a * t + b

/-- Vieta's identity on the trace-one hyperplane. -/
theorem traceOneCubic_eq_prod {R : Type*} [CommRing R] (α β γ t : R)
    (htrace : α + β + γ = 1) :
    traceOneCubic (secondCoeff α β γ) (constantCoeff α β γ) t =
      (t - α) * (t - β) * (t - γ) := by
  unfold traceOneCubic secondCoeff constantCoeff
  calc
    _ = t ^ 3 - (α + β + γ) * t ^ 2 +
        (α * β + β * γ + γ * α) * t - α * β * γ := by rw [htrace]; ring
    _ = _ := by ring

end Cubic.OrbitParametrization
