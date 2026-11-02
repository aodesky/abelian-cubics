import Cubic.BoxAsymptotic.PrimitiveHeckeData

/-! Authorized literature input: Iwaniec--Kowalski, Analytic Number Theory,
Theorem 3.8 and (3.83)--(3.88), with vertical growth from Lemma 5.2.
This is an explicit hypothesis, not an axiom or a proof of `lem:moment`.
Its arithmetic hypotheses must be verified for each actual character.
-/

namespace CubicTargets.BoxAsymptotic.PrimitiveHecke

open Cubic.PoissonSummation.CyclotomicIntegerUnits
open Cubic.BoxAsymptotic.PrimitiveHeckeData

def BlackBox : Prop :=
  ∀ (R : Type) [CommRing R] [Fintype R]
    (red : Integers →+* R) (χ : Rˣ →* ℂ) (k : ℤ) (ψ : Ideal Integers →*₀ ℂ),
    ArithmeticData red χ k ψ → k ≠ 0 →
    ∃ (L Λ : ℂ → ℂ) (ε : ℂ), AnalyticData ψ (scale R) k L Λ ε

end CubicTargets.BoxAsymptotic.PrimitiveHecke
