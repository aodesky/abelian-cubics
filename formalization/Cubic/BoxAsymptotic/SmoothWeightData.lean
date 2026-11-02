import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Logic.Function.Iterate

/-! The normalized differential operators in `lem:smooth`. These are definitions,
not assumptions about the angular counting measure or a proof of the estimate. -/

noncomputable section

namespace Cubic.BoxAsymptotic.SmoothWeightData

/-- The radial differential operator `n ∂_n`. -/
def radialDerivative (w : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : ℝ :=
  x.1 * deriv (fun n => w (n, x.2)) x.1

/-- The normalized angular differential operator `Θ ∂_θ`. -/
def angularDerivative (Θ : ℝ) (w : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : ℝ :=
  Θ * deriv (fun θ => w (x.1, θ)) x.2

/-- All mixed normalized derivatives through total order `J`, including the function. -/
def normalizedDerivativeBound (w : ℝ × ℝ → ℝ) (Θ M : ℝ) (J : ℕ) : Prop :=
  ∀ j ℓ : ℕ, j + ℓ ≤ J → ∀ x : ℝ × ℝ,
    |(radialDerivative^[j]) ((angularDerivative Θ)^[ℓ] w) x| ≤ M

theorem normalizedDerivativeBound.mono {w : ℝ × ℝ → ℝ} {Θ M : ℝ} {J K : ℕ}
    (h : normalizedDerivativeBound w Θ M J) (hK : K ≤ J) :
    normalizedDerivativeBound w Θ M K :=
  fun j ℓ hjℓ => h j ℓ (hjℓ.trans hK)

end Cubic.BoxAsymptotic.SmoothWeightData
