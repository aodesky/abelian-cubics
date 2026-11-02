import Cubic.BoxAsymptotic.MuSum

/-!
# One dyadic piece of the leading term, via `SmoothSectorCounting`

For `X ≥ 2`, `0 < Θ ≤ 1/4` and `θ₀`, write `τ = |wrap(θ - θ₀)|`. Then
`H/(nτ) φ(n/X) φ(τ/Θ) = (H/(XΘ)) Φ(n/X) Ψ(wrap(θ - θ₀)/Θ)`, so

  `Σ_{(n, β)} H/(nτ) φ(n/X) φ(τ/Θ) = (6H/(XΘ)) Σ_n ∫ w dμ_n`

and `SmoothSectorCounting` evaluates the right side with main term
`(6H/(XΘ)) (Θ log 2/π) X ((a log X + b₀) log 2 + a c₁)`
`= (6 log 2/π) H ((a log X + b₀) log 2 + a c₁)`, independent of `Θ` and `θ₀`, and error
`(6H/(XΘ)) Cst √X log(2X + 1/Θ)^A`.
-/

noncomputable section

namespace Cubic.BoxAsymptotic.Pieces

open CubicTargets.BoxAsymptotic (eis admissible muIntegral wrap weight aStar SmoothSectorCounting)
open Cubic.BoxAsymptotic.Admissible Cubic.BoxAsymptotic.SmoothPartition
open Cubic.BoxAsymptotic.PartitionIntegrals (c₁ main_integral)
open scoped ContDiff

/-- `τ = |wrap(θ - θ₀)|`. -/
def τof (θ₀ θ : ℝ) : ℝ := |wrap (θ - θ₀)|

/-- The piece weight `φ(n/X) φ(τ/Θ)`. -/
def pw (X Θ θ₀ n θ : ℝ) : ℝ := φ (n / X) * φ (τof θ₀ θ / Θ)

theorem pw_nonneg (X Θ θ₀ n θ : ℝ) : 0 ≤ pw X Θ θ₀ n θ :=
  mul_nonneg (φ_nonneg _) (φ_nonneg _)

theorem pointwise {H X Θ θ₀ n θ : ℝ} (hX : 0 < X) (hΘ : 0 < Θ) (hn : 0 < n) :
    H / (n * τof θ₀ θ) * pw X Θ θ₀ n θ = H / (X * Θ) * weight Φ Ψ X Θ θ₀ n θ := by
  simp only [pw, weight, Φ, Ψ, τof]
  rw [abs_div, abs_of_pos hΘ]
  rcases eq_or_lt_of_le (abs_nonneg (wrap (θ - θ₀))) with h0 | h0
  · rw [← h0]; simp
  · field_simp

/-- The data extracted from the hypothesis for our profiles. -/
theorem hyp_data (h : SmoothSectorCounting) : ∃ b₀ A Cst : ℝ, ∀ X Θ θ₀ : ℝ, 2 ≤ X → 0 < Θ →
    Θ ≤ 1 / 4 →
    |(∑ n ∈ Finset.range (⌊4 * X⌋₊ + 1), muIntegral n (weight Φ Ψ X Θ θ₀ n)) -
        Θ * Real.log 2 / Real.pi * X * ((aStar * Real.log X + b₀) * Real.log 2 + aStar * c₁)| ≤
      Cst * Real.sqrt X * Real.log (2 * X + 1 / Θ) ^ A := by
  obtain ⟨b₀, hb⟩ := h
  obtain ⟨A, Cst, hAC⟩ := hb Φ Ψ Φ_contDiff Ψ_contDiff Φ_support Ψ_support
  refine ⟨b₀, A, Cst, fun X Θ θ₀ hX hΘ hΘ' => ?_⟩
  have := hAC X Θ θ₀ hX hΘ hΘ'
  rwa [main_integral (by linarith) hΘ hΘ'] at this

/-- **One piece.** -/
theorem piece {H X Θ θ₀ b₀ A Cst : ℝ} (hX : 2 ≤ X) (hΘ : 0 < Θ) (hΘ' : Θ ≤ 1 / 4)
    (hXN : 2 * X ≤ Nmax H)
    (hd : |(∑ n ∈ Finset.range (⌊4 * X⌋₊ + 1), muIntegral n (weight Φ Ψ X Θ θ₀ n)) -
        Θ * Real.log 2 / Real.pi * X * ((aStar * Real.log X + b₀) * Real.log 2 + aStar * c₁)| ≤
      Cst * Real.sqrt X * Real.log (2 * X + 1 / Θ) ^ A) (hH : 0 ≤ H) :
    |(∑ x ∈ Bset H, H / (x.1 * τof θ₀ (θ x.2)) * pw X Θ θ₀ x.1 (θ x.2)) -
        6 * Real.log 2 / Real.pi * H * ((aStar * Real.log X + b₀) * Real.log 2 + aStar * c₁)| ≤
      6 * H / (X * Θ) * (Cst * Real.sqrt X * Real.log (2 * X + 1 / Θ) ^ A) := by
  have hX0 : 0 < X := by linarith
  have hsum : ∑ x ∈ Bset H, H / (x.1 * τof θ₀ (θ x.2)) * pw X Θ θ₀ x.1 (θ x.2) =
      6 * H / (X * Θ) * ∑ n ∈ Finset.range (⌊4 * X⌋₊ + 1), muIntegral n (weight Φ Ψ X Θ θ₀ n) := by
    have e1 : ∀ x ∈ Bset H, H / (x.1 * τof θ₀ (θ x.2)) * pw X Θ θ₀ x.1 (θ x.2) =
        H / (X * Θ) * weight Φ Ψ X Θ θ₀ x.1 (θ x.2) := fun x hx => by
      have h1 := (mem_Bset.mp (by simpa using hx : (x.1, x.2) ∈ Bset H)).1
      exact pointwise hX0 hΘ (by exact_mod_cast h1)
    rw [Finset.sum_congr rfl e1, ← Finset.mul_sum,
      MuSum.sum_Bset H (fun n θ => weight Φ Ψ X Θ θ₀ n θ),
      MuSum.sum_range_eq (by linarith) hXN (fun n θ => weight Φ Ψ X Θ θ₀ n θ)
        (fun n θ hw => ?_)]
    · ring
    · have hΦ : Φ (n / X) ≠ 0 := fun h0 => hw (by simp [weight, h0])
      have := Φ_support hΦ
      have hφ : φ (n / X) ≠ 0 := fun h0 => hΦ (by rw [Φ, h0, zero_div])
      have h2 := φ_support hφ
      have a1 := (le_div_iff₀ hX0).mp h2.1
      have a2 := (div_le_iff₀ hX0).mp h2.2
      constructor <;> linarith
  rw [hsum]
  have hc : 0 ≤ 6 * H / (X * Θ) := by positivity
  have e2 : 6 * Real.log 2 / Real.pi * H * ((aStar * Real.log X + b₀) * Real.log 2 + aStar * c₁) =
      6 * H / (X * Θ) * (Θ * Real.log 2 / Real.pi * X *
        ((aStar * Real.log X + b₀) * Real.log 2 + aStar * c₁)) := by
    field_simp
  rw [e2, ← mul_sub, abs_mul, abs_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left hd hc

end Cubic.BoxAsymptotic.Pieces
