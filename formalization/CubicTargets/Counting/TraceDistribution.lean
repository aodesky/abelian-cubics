import CubicTargets.Counting.GeneralMonic

/-!
# Target for `thm:traceDistribution`

For `r ∈ {0, 1, 2}` and `-1 ≤ u₁ ≤ u₂ ≤ 1`,
`N_r(H; u₁, u₂) = #{f ∈ F_mon : H(f) ≤ H, Tr(f) ≡ r (mod 3), u₁ ≤ Tr(f)/H ≤ u₂}`.
The claim states finiteness of these sets, the asymptotic formula with an `O(H³)` error
whose constant and threshold are uniform in `r`, `u₁`, `u₂`, the limiting proportions
`5/11`, `3/11`, `3/11` of the three residue classes among the polynomials counted in
`thm:generalMonicCount` (`generalSet H`), and the limiting density `(3/20)(3 + u²)` of
`Tr(f)/H` within each residue class, stated as convergence of the proportion with
`u₁ ≤ Tr(f)/H ≤ u₂` to `∫_{u₁}^{u₂} (3/20)(3 + u²) du`.
-/

noncomputable section

namespace CubicTargets.Counting.TraceDistribution

open Filter Polynomial
open Cubic.Counting.GeneralMonicData Cubic.Counting.IntegralPointCountData
open scoped Topology

/-- The polynomials counted by `N_r(H; u₁, u₂)`. -/
def traceSet (r : ℤ) (H u₁ u₂ : ℝ) : Set ℤ[X] :=
  {f | f ∈ generalSet H ∧
    (trace f ≡ r [ZMOD 3] ∧ u₁ ≤ (trace f : ℝ) / H ∧ (trace f : ℝ) / H ≤ u₂)}

/-- `N_r(H; u₁, u₂)`. -/
def N (r : ℤ) (H u₁ u₂ : ℝ) : ℕ := Nat.card (traceSet r H u₁ u₂)

/-- `c₀ = 5α/81`, `c₁ = c₂ = α/27`. -/
def c (r : ℤ) : ℝ := if r = 0 then 5 * alpha / 81 else alpha / 27

/-- `thm:traceDistribution`. -/
def Claim : Prop :=
  (∀ (r : ℤ) (H u₁ u₂ : ℝ), (traceSet r H u₁ u₂).Finite) ∧
  -- the asymptotic formula, uniformly in `r`, `u₁`, `u₂`
  (∃ K H₀ : ℝ, ∀ H : ℝ, H₀ ≤ H → ∀ r ∈ ({0, 1, 2} : Set ℤ), ∀ u₁ u₂ : ℝ,
    -1 ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ 1 →
      |(N r H u₁ u₂ : ℝ) - c r * (∫ u in u₁..u₂, (3 + u ^ 2)) * H ^ 3 * Real.log H| ≤
        K * H ^ 3) ∧
  -- the proportions of the three residue classes
  Tendsto (fun H => (N 0 H (-1) 1 : ℝ) / Nat.card (generalSet H)) atTop (𝓝 (5 / 11)) ∧
  Tendsto (fun H => (N 1 H (-1) 1 : ℝ) / Nat.card (generalSet H)) atTop (𝓝 (3 / 11)) ∧
  Tendsto (fun H => (N 2 H (-1) 1 : ℝ) / Nat.card (generalSet H)) atTop (𝓝 (3 / 11)) ∧
  -- the limiting density `(3/20)(3 + u²)` within each residue class
  ∀ r ∈ ({0, 1, 2} : Set ℤ), ∀ u₁ u₂ : ℝ, -1 ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ 1 →
    Tendsto (fun H => (N r H u₁ u₂ : ℝ) / N r H (-1) 1) atTop
      (𝓝 (∫ u in u₁..u₂, 3 / 20 * (3 + u ^ 2)))

end CubicTargets.Counting.TraceDistribution
