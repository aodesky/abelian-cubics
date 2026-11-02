import Cubic.Counting.GeneralMonicData
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The box-height count of monic abelian cubics

[Xiao, *On monic abelian cubics*, Compos. Math. 158 (2022), 550–567, arXiv:1906.08625,
Theorem 1.1] states: "Let `C₃` be the cyclic group of order 3 and `N_{C₃}^{(3)}(X)` given as
in (1.2). Then there exist positive numbers `k₁, k₂` such that for all `X > k₂` we have
`2X ≤ N_{C₃}^{(3)}(X) < k₁ X (log X)²`", where (1.1)–(1.2) define
`N_G^{(n)}(X) = #{f = xⁿ + a₁xⁿ⁻¹ + ⋯ + aₙ ∈ ℤ[x] : H(f) ≤ X, Gal(f) ≅ G}` with the box
height `H(f) = max |aᵢ|`.

`XiaoUpperBound` is the upper-bound half of that statement. The note
`box_height_research_note.tex` asserts that `N_{C₃}^{(3)}(X) / (X (log X)²) → ∞`
(`UnboundedRatio`), which contradicts it.
-/

noncomputable section

namespace CubicTargets.BoxHeight

open Polynomial Filter Cubic.Counting.GeneralMonicData
open Cubic.QuadraticCorrespondence.CorrespondencePolynomials

/-- Monic integral cubics with Galois group `C₃` and box height at most `X`. -/
def boxSet (X : ℝ) : Set ℤ[X] :=
  {f | (∃ a₂ a₁ a₀ : ℤ, f = monicCubic a₂ a₁ a₀ ∧
      (|a₂| : ℝ) ≤ X ∧ (|a₁| : ℝ) ≤ X ∧ (|a₀| : ℝ) ≤ X) ∧
    HasCyclicCubicGaloisGroup (f.map (Int.castRingHom ℚ))}

/-- `N_{C₃}^{(3)}(X)`. -/
def boxCount (X : ℝ) : ℕ := Nat.card (boxSet X)

/-- The upper bound of [Xiao, Theorem 1.1]. -/
def XiaoUpperBound : Prop :=
  ∃ k₁ k₂ : ℝ, 0 < k₁ ∧ 0 < k₂ ∧ ∀ X : ℝ, k₂ < X → (boxCount X : ℝ) < k₁ * X * Real.log X ^ 2

/-- The counts are finite and `N_{C₃}^{(3)}(X) / (X (log X)²) → ∞`. -/
def UnboundedRatio : Prop :=
  (∀ X : ℝ, (boxSet X).Finite) ∧
    Tendsto (fun X : ℝ => (boxCount X : ℝ) / (X * Real.log X ^ 2)) atTop atTop

end CubicTargets.BoxHeight
