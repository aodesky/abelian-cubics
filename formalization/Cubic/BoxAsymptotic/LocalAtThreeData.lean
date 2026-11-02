import Cubic.BoxAsymptotic.AngularIdealData

/-! Independent objects in the full local table `lem:local3`. The left side
uses the original polynomial-integrality congruences, and the right side uses
the actual global units, primary elements, and `λ=1-ζ` in the ring of integers. -/

noncomputable section

namespace Cubic.BoxAsymptotic.LocalAtThreeData

open Cubic.PoissonSummation.CyclotomicIntegerUnits
open Cubic.Counting.EisensteinNormCount
open Cubic.BoxAsymptotic.AngularLocalData

/-- The prime element `λ=1-ζ` with the paper's chosen sign. -/
def lambda : Integers := 1 - zetaInteger

/-- Norm compatibility and all three congruences in `eq:cong`, for a specified trace. -/
def AdmissiblePair (n : ℕ) (β : ℤ × ℤ) (s : ℤ) : Prop :=
  β ∈ normSet ((n : ℤ) ^ 3) ∧ (3 : ℤ) ∣ β.2 ∧
    s ^ 2 ≡ n [ZMOD 3] ∧ 2 * β.1 - β.2 ≡ 3 * s * n - s ^ 3 [ZMOD 27]

/-- The generators and trace residues displayed in `lem:local3`. -/
def TableEntry (e M : ℕ) (β : ℤ × ℤ) (s : ℤ) : Prop :=
  match e with
  | 0 => (β ∈ primary M ∧ s ≡ 1 [ZMOD 3]) ∨
      (∃ α ∈ primary M, β = -α ∧ s ≡ -1 [ZMOD 3])
  | 1 => (∃ α ∈ primary M, coord β = lambda ^ 3 * coord α ∨
      coord β = -(lambda ^ 3 * coord α)) ∧ s ≡ 0 [ZMOD 3]
  | e + 2 => (∃ (u : Integersˣ) (α : ℤ × ℤ), α ∈ primary M ∧
      coord β = (u : Integers) * lambda ^ (3 * (e + 2)) * coord α) ∧ s ≡ 0 [ZMOD 3]

end Cubic.BoxAsymptotic.LocalAtThreeData
