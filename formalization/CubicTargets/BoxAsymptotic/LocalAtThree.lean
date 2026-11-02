import Cubic.BoxAsymptotic.LocalAtThreeData

/-! The complete target for `lem:local3`, including the assigned trace residue
for each generator and the assertion that every trace in that class works. -/

namespace CubicTargets.BoxAsymptotic

open Cubic.BoxAsymptotic.LocalAtThreeData

/-- The full local table at three, not merely its mass or Fourier coefficients. -/
def LocalAtThreeClaim : Prop :=
  (∀ (e M : ℕ), ¬ 3 ∣ M → ∀ (β : ℤ × ℤ) (s : ℤ),
    AdmissiblePair (3 ^ e * M) β s ↔ TableEntry e M β s) ∧
  (∀ (n : ℕ) (β : ℤ × ℤ) (s₀ : ℤ), AdmissiblePair n β s₀ →
    ∀ s : ℤ, AdmissiblePair n β s ↔ s ≡ s₀ [ZMOD 3])

end CubicTargets.BoxAsymptotic
