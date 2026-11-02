import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! General Dirichlet-series data for the degree-two approximate functional
equation, with a single complex Gamma factor. There are no Hecke characters
or moment estimates in these definitions. -/

noncomputable section

namespace Cubic.Analysis.GammaAFEData

def completedFactor (Q κ : ℝ) (s : ℂ) : ℂ :=
  (Q : ℂ) ^ s * Complex.Gamma (s + κ)

def VerticalGrowth (L : ℂ → ℂ) : Prop :=
  ∀ a b : ℝ, a ≤ b → ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ,
    ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖L s‖ ≤ C * (1 + |s.im|) ^ N

structure AnalyticData (a : ℕ → ℂ) (Q κ : ℝ) (L Λ : ℂ → ℂ) (ε : ℂ) : Prop where
  entire : Differentiable ℂ L
  completed_entire : Differentiable ℂ Λ
  absolute : ∀ s : ℂ, 1 < s.re → LSeriesSummable a s
  series_eq : ∀ s : ℂ, 1 < s.re → L s = LSeries a s
  completion_eq : ∀ s : ℂ, 0 < s.re → Λ s = completedFactor Q κ s * L s
  root_number : ‖ε‖ = 1
  functional_equation : ∀ s : ℂ, Λ s = ε * star (Λ (1 - star s))
  growth : VerticalGrowth L

/-- Iwaniec--Kowalski's auxiliary function with degree `d=2` and decay order
`A=3`. Its first poles are at real parts `±6`, outside the contour strip. -/
def auxiliary (z : ℂ) : ℂ := (Complex.cos ((Real.pi : ℂ) * z / 12))⁻¹ ^ 24

/-- The contour `Re z=3`, parametrized by real imaginary part. The factor `i`
in `dz` cancels the `i` in `1/(2πi)`. -/
def weight (Q κ : ℝ) (u : ℂ) (x : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ))⁻¹ * ∫ v : ℝ,
    let z : ℂ := 3 + v * Complex.I
    auxiliary z * (Q : ℂ) ^ z *
      (Complex.Gamma (u + κ + z) / Complex.Gamma (u + κ)) *
      (x : ℂ) ^ (-z) / z

/-- The textbook's `sqrt(q q_∞(u))`, after duplication of the Gamma factor:
the two real-Gamma shifts are `κ,κ+1`, and `sqrt(q)=2πQ`. -/
def length (Q κ : ℝ) (u : ℂ) : ℝ :=
  2 * Real.pi * Q * Real.sqrt ((‖u + κ‖ + 3) * (‖u + κ + 1‖ + 3))

def dualFactor (Q κ : ℝ) (ε s : ℂ) : ℂ :=
  ε * (Q : ℂ) ^ (1 - 2 * s) *
    (Complex.Gamma (1 - s + κ) / Complex.Gamma (s + κ))

def weightedTerm (a : ℕ → ℂ) (Q κ : ℝ) (u : ℂ) (n : ℕ) : ℂ :=
  LSeries.term a u n * weight Q κ u n

end Cubic.Analysis.GammaAFEData
