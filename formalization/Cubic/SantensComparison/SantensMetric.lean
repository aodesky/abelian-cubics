import Cubic.SantensComparison.ToricPairData

/-! Finite local metrics admitted by Santens, arXiv:2312.13914v2.

Definition 4.1 requires the local norms at a prime `p` to lie in `p^ℤ ∪ {0}`.
Definition 4.14 requires an adelic metric to be integral for one integral
model at all but finitely many places. By Definition 3.8(3), at the primes
the adelic space of `(X;A)` involves only points of `U`.

`FiniteMetric P φ ψ` is a sufficient toric condition for `ψ` to be the
family of finite local metrics of a height on the class read from `φ`:

* each `ψ p` is a piecewise-linear support function on the fan;
* `ψ p` agrees with `φ` on the open rays. Both are linear on every cone, so
  they agree on the cones of `U`, and near each boundary point of `U(ℚ_p)`
  their quotient depends only on bounded valuation data. The quotient of
  the local metrics is therefore a continuous positive function on `U(ℚ_p)`,
  and both are metrics on the same line bundle on `U`;
* the local norms lie in `p^ℤ`;
* outside a finite set of primes, `ψ p` is one support function with integral
  characters on every cone. It is the model metric of an integral toric
  Cartier divisor, which is integral at those primes.

This is a narrowing of Santens's class of heights, not an enlargement. -/

noncomputable section

namespace Cubic.SantensComparison.SantensMetric

open ToricFanData ToricMetricData ToricMetricGeometry ToricPairData

/-- A support function given on each cone by an integral character. -/
def IntegralCharacters (F : Fan) (ψ : Support) : Prop :=
  ∀ i, ∃ m : ℤ × ℤ, ∀ v ∈ F.cone i,
    ψ (ambientCoordinates v)=((m.1:ℝ)*v.1+(m.2:ℝ)*v.2 : ℝ)

/-- Finite local metrics in the sense of Santens's Definitions 4.1 and 4.14,
for the height whose real-place support function is `φ`. -/
structure FiniteMetric (P : Pair) (φ : Support) (ψ : FiniteSupport) : Prop where
  toric : ∀ p, CanonicalMetric P.fan (ψ p)
  open_rays : ∀ p i, i ∉ P.boundary →
    ψ p (ambientCoordinates (P.fan.realRay i))=φ (ambientCoordinates (P.fan.realRay i))
  values : ∀ p x, ∃ m : ℤ, finiteHeight (ψ p) p x=((p:ℕ):ℂ)^m
  integral : ∃ S : Finset Nat.Primes, ∃ ψ₀ : Support,
    IntegralCharacters P.fan ψ₀ ∧ ∀ p ∉ S, ψ p=ψ₀

end Cubic.SantensComparison.SantensMetric
