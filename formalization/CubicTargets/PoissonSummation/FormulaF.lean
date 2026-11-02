import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Concrete statement of `formula_f(z)`

In the former longer proof of `lemma:simplifiedZ(s)` (retained as historical mathematics):
```text
∏_{p≡1 (3)} (1 + 3/p^z · (1 − 1/p^z)^{-1}) · ∏_{p≡1 (3)} (1 − 1/p^z)^3
    = ∏_{p≡1 (3)} (1 − 3/p^{2z} + 2/p^{3z}).
```
The TeX does not state the region. It is used in the half-plane of absolute
convergence `Re z > 1`, where all three products converge (the first two need
`Re z > 1`); the claim is stated there, with convergence of each product
(`Multipliable`) as part of the claim, since `∏'` is only meaningful for convergent
products. Products run over rational primes `p` with `p ≡ 1 (mod 3)`, and
`p^z` is the principal complex power `(p : ℂ) ^ z`.
-/

namespace CubicTargets.PoissonSummation.FormulaF

/-- Rational primes `p ≡ 1 (mod 3)`. -/
abbrev SplitPrimes := {p : Nat.Primes // (p : ℕ) % 3 = 1}

noncomputable def first (z : ℂ) (p : SplitPrimes) : ℂ :=
  1 + 3 / (p.1 : ℂ) ^ z * (1 - 1 / (p.1 : ℂ) ^ z)⁻¹

noncomputable def second (z : ℂ) (p : SplitPrimes) : ℂ :=
  (1 - 1 / (p.1 : ℂ) ^ z) ^ 3

noncomputable def third (z : ℂ) (p : SplitPrimes) : ℂ :=
  1 - 3 / (p.1 : ℂ) ^ (2 * z) + 2 / (p.1 : ℂ) ^ (3 * z)

structure Claim : Prop where
  multipliable_first : ∀ z : ℂ, 1 < z.re → Multipliable (first z)
  multipliable_second : ∀ z : ℂ, 1 < z.re → Multipliable (second z)
  multipliable_third : ∀ z : ℂ, 1 < z.re → Multipliable (third z)
  eq : ∀ z : ℂ, 1 < z.re →
    (∏' p, first z p) * (∏' p, second z p) = ∏' p, third z p

end CubicTargets.PoissonSummation.FormulaF
