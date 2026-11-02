import CubicTargets.BoxHeight.XiaoUpperBound
import Cubic.Counting.GeneralMonicData
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.Order.ToIntervalMod

/-!
# The sharp box-height asymptotic (`box_full_asymptotic.tex`)

`thm:main`: `N_□(H) = A₃ H (log H)³ + O(H (log H)² log log H)` with
`A₃ = 121 C / (27 π √3)`, where `N_□` is `CubicTargets.BoxHeight.boxCount` and `C` is the
leading constant of the trace-one count.

The original geometric reduction uses `SmoothSectorCounting`, stated below.
The final theorem now supplies it from the full proved `lem:smooth` via
`SmoothProductCounting.of_full`, retaining only the explicit literature inputs.
It is used only for weights of product form `Φ(n/X) Ψ((θ - θ₀)/Θ)` with fixed smooth
profiles and `Θ ≤ 1/4`; for these the normalized derivatives
`(n∂_n)^j (Θ∂_θ)^ℓ w` are bounded in terms of `Φ, Ψ` alone, so this special case is
implied by `lem:smooth`. The full target, including the second constant formula
and the final comparability assertion, is `FullMainClaim` in `Main.lean`.

The angular measure `μ_n` is defined from the congruences `eq:cong`: mass `1/6` at `arg β`
for each `β = A + Bζ ∈ ℤ[ζ]` with `N β = n³`, `3 ∣ B`, and some integer `s` with
`s² ≡ n (mod 3)`, `2A - B ≡ 3sn - s³ (mod 27)`. Here `ζ = (-1 + √-3)/2`,
`N(A + Bζ) = A² - AB + B²`, and `A + Bζ = (A - B/2) + (B√3/2) i` in `ℂ`.
-/

noncomputable section

namespace CubicTargets.BoxAsymptotic

open Cubic.Counting.GeneralMonicData

/-- `A + Bζ` as a complex number. -/
def eis (β : ℤ × ℤ) : ℂ := ⟨(β.1 : ℝ) - β.2 / 2, (β.2 : ℝ) * Real.sqrt 3 / 2⟩

/-- The pairs `(A, B)` admissible for `n` (`eq:cong`, with `N β = n³`). -/
def admissible (n : ℕ) : Set (ℤ × ℤ) :=
  {β | β.1 ^ 2 - β.1 * β.2 + β.2 ^ 2 = (n : ℤ) ^ 3 ∧ (3 : ℤ) ∣ β.2 ∧
    ∃ s : ℤ, s ^ 2 ≡ n [ZMOD 3] ∧ 2 * β.1 - β.2 ≡ 3 * s * n - s ^ 3 [ZMOD 27]}

open scoped Classical in
/-- `∫ g dμ_n = (1/6) Σ_{β admissible} g(arg β)`. -/
def muIntegral (n : ℕ) (g : ℝ → ℝ) : ℝ :=
  (1 / 6 : ℝ) * ∑ᶠ β ∈ admissible n, g (Complex.arg (eis β))

/-- The representative of `θ` in `(-π, π]`. -/
def wrap (θ : ℝ) : ℝ := toIocMod Real.two_pi_pos (-Real.pi) θ

/-- The product weight `w(n, θ) = Φ(n/X) Ψ(wrap(θ - θ₀)/Θ)`. -/
def weight (Φ Ψ : ℝ → ℝ) (X Θ θ₀ n θ : ℝ) : ℝ := Φ (n / X) * Ψ (wrap (θ - θ₀) / Θ)

/-- `a = 11C/54`, the double-pole coefficient of `F₀` at `1` (`eq:F0`). -/
def aStar : ℝ := 11 * Cconst / 54

open scoped ContDiff in
/-- `lem:smooth` for product weights: there is `b₀` such that for smooth (`C^∞`) profiles `Φ`
supported in `[1/2, 4]` and `Ψ` supported in `[-4, 4]`, with `X ≥ 2` and `0 < Θ ≤ 1/4`,
`Σ_n ∫ w dμ_n = ∫_0^∞ ∫_0^{2π} w(n, θ) (a log n + b₀) dθ/(2π) dn
  + O_{Φ,Ψ}(√X (log(2X + Θ⁻¹))^A)`. -/
def SmoothSectorCounting : Prop :=
  ∃ b₀ : ℝ, ∀ Φ Ψ : ℝ → ℝ, ContDiff ℝ ∞ Φ → ContDiff ℝ ∞ Ψ →
    Function.support Φ ⊆ Set.Icc (1 / 2) 4 → Function.support Ψ ⊆ Set.Icc (-4) 4 →
    ∃ A Cst : ℝ, ∀ X Θ θ₀ : ℝ, 2 ≤ X → 0 < Θ → Θ ≤ 1 / 4 →
      |(∑ n ∈ Finset.range (⌊4 * X⌋₊ + 1), muIntegral n (weight Φ Ψ X Θ θ₀ n)) -
          ∫ n in Set.Ioi (0 : ℝ), ∫ θ in (0 : ℝ)..2 * Real.pi,
            weight Φ Ψ X Θ θ₀ n θ * (aStar * Real.log n + b₀) / (2 * Real.pi)| ≤
        Cst * Real.sqrt X * Real.log (2 * X + 1 / Θ) ^ A

/-- `A₃ = 121 C / (27 π √3)`. -/
def A3 : ℝ := 121 * Cconst / (27 * Real.pi * Real.sqrt 3)

/-- `thm:main`: `N_□(H) = A₃ H (log H)³ + O(H (log H)² log log H)`. -/
def MainClaim : Prop :=
  ∃ K H₀ : ℝ, ∀ H : ℝ, H₀ ≤ H →
    |(CubicTargets.BoxHeight.boxCount H : ℝ) - A3 * H * Real.log H ^ 3| ≤
      K * H * Real.log H ^ 2 * Real.log (Real.log H)

end CubicTargets.BoxAsymptotic
