import Cubic.PoissonSummation.AdelicData
import Cubic.PoissonSummation.RationalAdelicEmbedding
import Cubic.QuadraticCorrespondence.QuotientNormCharacter

/-!
# Concrete statement of `eqn:LAsNorm`

For `x ∈ T(𝔸)`, `ℓ(x)(N) = -log |N(x)|_𝔸`, where `N : T → 𝔾_m` is the norm character and
`N(x) ∈ 𝔸^×` its adelic value.

## Correspondence

* `T(𝔸)` is `AdelicData.Points` (original real points × restricted product of the original
  local point groups), and `ℓ(x) = ½ ∑_w ℓ_w(x_w) log q_w` is `AdelicData.logarithm`
  (weights `log q_w/[E:ℚ]`), in the ray coordinates `v₁ = (1,0)`, `v₂ = (0,1)` of `𝔱_E`.
* Characters `m = m₁a' + m₂b' ∈ M_E` pair with `n ∈ 𝔱_E` through their `v^∨`-coordinates
  `CharacterLattice.pullback m` (`pairing`); `N = a' + b' = (1,1)`, the character
  `QuotientNormCharacter.normCharacter` (the descended monomial `(1,1)`, whose value is the
  product of the two conjugate unit coordinates, i.e. the norm of `ι(x)`).
* `N(x_v)` is `QuotientNormCharacter.value ℚ_v x_v` (for finite `v`, after the identification
  `originalEquiv p` of the local group with `quotientFixedRing →ₐ[ℚ] ℚ_[p]`).
* `𝔸^×` is not an object of the project. As a documented equivalent,
  `|N(x)|_𝔸 := |N(x_∞)| · ∏'_p ‖N(x_p)‖_p` (`adelicNorm`), with the p-adic norm
  `‖·‖_p = p^{-ord_p}`. That `N(x_p)` is a unit for almost all `p`, so the product has finitely
  many factors `≠ 1`, is part of the claim (`finite_mulSupport`), not an assumption.
-/

noncomputable section

namespace CubicTargets.PoissonSummation.LAsNorm

open Cubic.QuadraticCorrespondence Cubic.PoissonSummation
open QuotientFiniteFourierProduct RationalAdelicEmbedding

local instance primeFact (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

/-- The pairing `⟨m, n⟩` of `m = m₁a' + m₂b' ∈ M_E` with `n ∈ 𝔱_E`. -/
def pairing (m : ℤ × ℤ) (n : ℝ × ℝ) : ℝ :=
  ((CharacterLattice.pullback m).1 : ℝ) * n.1 + ((CharacterLattice.pullback m).2 : ℝ) * n.2

/-- The norm character `N = a' + b'`. -/
def normCharacter : ℤ × ℤ := (1, 1)

/-- `N(x_p) ∈ ℚ_p^×`. -/
def localNorm (p : Nat.Primes) (y : (family p).Carrier) : ℚ_[p] :=
  (QuotientNormCharacter.value ℚ_[p] (originalEquiv p y) : ℚ_[p])

/-- `N(x_∞) ∈ ℝ^×`. -/
def infiniteNorm (P : Cubic.ToricHeights.ArchimedeanQuotientLogarithm.Points) : ℝ :=
  (QuotientNormCharacter.value ℝ P : ℝ)

/-- `|N(x)|_𝔸 = |N(x_∞)| · ∏'_p ‖N(x_p)‖_p`. -/
def adelicNorm (x : AdelicData.Points) : ℝ :=
  |infiniteNorm x.1| * ∏' p : Nat.Primes, ‖localNorm p (x.2 p)‖

structure Claim : Prop where
  finite_mulSupport : ∀ x : AdelicData.Points,
    (Function.mulSupport (fun p : Nat.Primes => ‖localNorm p (x.2 p)‖)).Finite
  eq : ∀ x : AdelicData.Points,
    pairing normCharacter (AdelicData.logarithm x) = -Real.log (adelicNorm x)

end CubicTargets.PoissonSummation.LAsNorm
