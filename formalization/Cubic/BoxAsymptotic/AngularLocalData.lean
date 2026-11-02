import Cubic.BoxAsymptotic.AngularSeriesData

/-! Independent finite sums used to compute the local factor at three in `eq:Fk`.
`primary M` is the coordinate description of the primary elements of norm `M³`;
its identification with primary ideal generators is proved in `AngularIdeals`. -/

noncomputable section

namespace Cubic.BoxAsymptotic.AngularLocalData

open CubicTargets.BoxAsymptotic Cubic.BoxAsymptotic.AngularSeriesData
open Cubic.Counting.EisensteinNormCount Cubic.Counting.TraceZeroLattice

/-- Elements congruent to `1` modulo `3𝒪`, of norm `M³`. -/
def primary (M : ℕ) : Set (ℤ × ℤ) :=
  {p | p ∈ normSet ((M : ℤ) ^ 3) ∧ p.1 ≡ 1 [ZMOD 3] ∧ 3 ∣ p.2}

/-- The angular sum over a finite set of lattice points. -/
def angularSum (k : ℤ) (S : Set (ℤ × ℤ)) : ℂ := ∑ᶠ p ∈ S, phase k (eis p)

/-- The coefficients of `D_k`, with the factor at `3` omitted. -/
def awayCoefficient (k : ℤ) (M : ℕ) : ℂ :=
  if 3 ∣ M then 0 else angularSum k (primary M)

/-- Independent element description of the angular Dirichlet series away from `3`.
For even `k`, the paper identifies this with its ideal-character series `D_k`. -/
def awaySeries (k : ℤ) (s : ℂ) : ℂ := LSeries (awayCoefficient k) s

/-- Multiplication by `λ³ = -3-6ζ` rotates by `-π/2`. -/
def ramifiedPhase (k : ℤ) : ℂ := (-Complex.I) ^ k

/-- The coefficient at the `e`th power of `3` in `eq:Fk`. -/
def localWeight (k : ℤ) (e : ℕ) : ℂ :=
  (if e < 2 then (1 / 3 : ℂ) else if 6 ∣ k then 1 else 0) * ramifiedPhase k ^ e

end Cubic.BoxAsymptotic.AngularLocalData
