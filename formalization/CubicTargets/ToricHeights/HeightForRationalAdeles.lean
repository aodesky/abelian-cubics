import Cubic.PoissonSummation.AdelicHeightZetaData

/-!
# Concrete statement of `eqn:heightforrationaladeles`

For `x = (x_v)_v ∈ T(𝔸)` embedded diagonally in `T(𝔸_E)`, `φ(ℓ_w(x_v))` does not depend on
the choice of `w` over `v`, and
```text
H(x, φ) = ∏_{v ∈ Pl_ℚ} q_v^{-(1/e_v) φ(ℓ_w(x_v))}.
```

## Correspondence

* `T(𝔸)` is `AdelicData.Points`: the original real points times the restricted product of
  the original local point groups `(family p).Carrier` (≃ `quotientFixedRing →ₐ[ℚ] ℚ_[p]`).
* `T(𝔸_E)` and the product over `Pl_E` are not objects of the project. The project's height
  `H(x, φ)` (`AdelicHeightZetaData.height s₀ σ`, i.e. the inverse height at `-(s₀,σ)`) is
  constructed as the paper's definition `∏_{w ∈ Pl_E} (q_w^{-φ(ℓ_w(x_w))})^{1/[E:ℚ]}` with the
  `Pl_E` factors grouped by the rational place below them: at a split prime the two factors of
  `splitInverseHeight`, at the inert and ramified primes and at infinity the single factor
  (with the residue cardinality `q_w` of the actual local integer ring and `[E:ℚ] = 2`).
  The claim below is the displayed identity for this height.
* `φ` ranges over all support functions, i.e. `supportFunction s₀ σ` for `s₀, σ ∈ ℂ`
  (`Γ`-invariant divisors `(s₀, σ, σ)`, `φ(v_e) = -s_e`).
* `ℓ_w(x_v)` is the project's local cocharacter at one chosen place `w | v`
  (`placeCocharacter`): `splitCoordinates` (first split place), `inertCoordinates`,
  `ramifiedCoordinates`, and `ArchimedeanQuotientLogarithm.localCocharacter` at infinity.
  Independence of `w` at a split prime (the only case with two places) is part of the claim.
* `q_v = p` for `v = p` and `q_∞ = e` (the `q_w` of the place of `ℚ`, as in the paper's
  convention `q_w = e` for a real place); `e_v` is the ramification index: `2` at `3`,
  otherwise `1`, and `e_∞ = 1`.
* The infinite product is a `tprod`; its convergence (`Multipliable`) is part of the claim.
-/

noncomputable section

namespace CubicTargets.ToricHeights.HeightForRationalAdeles

open Cubic.ToricHeights Cubic.PoissonSummation QuotientFiniteHeight
open QuotientFiniteFourierProduct QuotientLocalFourier FiniteEulerProduct

/-- `ℓ_w(x_p)` at the chosen place `w` of `E` over `p`. -/
def placeCocharacter (p : Nat.Primes) : (family p).Carrier → ℝ × ℝ := by
  haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
  by_cases hs : (p : ℕ) % 3 = 1
  · haveI : Fact ((p : ℕ) % 3 = 1) := ⟨hs⟩
    rw [family_split ⟨p, hs⟩]
    exact splitCoordinates p
  by_cases hi : (p : ℕ) % 3 = 2
  · haveI : Fact ((p : ℕ) % 3 = 2) := ⟨hi⟩
    rw [family_inert ⟨p, hi⟩]
    exact inertCoordinates p
  · have h : family p = ramifiedData := by simp [family, hs, hi]
    rw [h]
    exact ramifiedCoordinates

/-- The ramification index `e_p` of `p` in `E = ℚ(ζ₃)`. -/
def ramificationIndex (p : Nat.Primes) : ℕ := if (p : ℕ) = 3 then 2 else 1

/-- The factor `q_p^{-(1/e_p) φ(ℓ_w(x_p))}`. -/
def localFactor (s₀ σ : ℂ) (p : Nat.Primes) (y : (family p).Carrier) : ℂ :=
  (p : ℂ) ^ (-supportFunction s₀ σ (placeCocharacter p y) / (ramificationIndex p : ℂ))

structure Claim : Prop where
  /-- At a split prime `φ(ℓ_w(x_p))` is the same for both places `w | p`. -/
  independent : ∀ (p : ℕ) [Fact p.Prime] [Fact (p % 3 = 1)] (s₀ σ : ℂ)
    (P : Cubic.QuadraticCorrespondence.CyclotomicTorusGalois.quotientFixedRing →ₐ[ℚ] ℚ_[p]),
    supportFunction s₀ σ (splitSecondCoordinates p P) = supportFunction s₀ σ (splitCoordinates p P)
  multipliable : ∀ (s₀ σ : ℂ) (x : AdelicData.Points),
    Multipliable (fun p : Nat.Primes => localFactor s₀ σ p (x.2 p))
  height_eq : ∀ (s₀ σ : ℂ) (x : AdelicData.Points),
    AdelicHeightZetaData.height s₀ σ x =
      (Real.exp 1 : ℂ) ^ (-supportFunction s₀ σ (ArchimedeanQuotientLogarithm.localCocharacter x.1)) *
        ∏' p : Nat.Primes, localFactor s₀ σ p (x.2 p)

end CubicTargets.ToricHeights.HeightForRationalAdeles
