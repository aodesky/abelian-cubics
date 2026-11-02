import CubicTargets.BoxHeight.XiaoUpperBound
import Cubic.Counting.AsymptoticConstantsData

/-!
# `thm:lower` of `box_height_research_note.tex`

"There exists an absolute constant `A` such that, for sufficiently large `H`,
`N_□(H) ≥ (11C/(27π√3)) H (log H)³ − A H (log H)²`."

Here `N_□(H)` is `boxCount H`, the number of monic integral cubics with Galois group `C₃`
and all coefficients at most `H` in absolute value, and
`C = (4π²/81) R(1)` with `R(1) = ∏_{q ≡ 2 (3)} (1 − q^{−2}) ∏_{p ≡ 1 (3)} (1 − 3p^{−2} + 2p^{−3})`,
which is `AsymptoticConstantsData.originalLeading`. The counts are finite (`boxSet_finite`),
so `boxCount` is the number of such polynomials.
-/

noncomputable section

namespace CubicTargets.BoxHeight

open Cubic.Counting.AsymptoticConstantsData

/-- `thm:lower`. -/
def LowerClaim : Prop :=
  (∀ X : ℝ, (boxSet X).Finite) ∧
    ∃ A H₀ : ℝ, ∀ H : ℝ, H₀ ≤ H →
      11 * originalLeading / (27 * Real.pi * Real.sqrt 3) * H * Real.log H ^ 3 -
          A * H * Real.log H ^ 2 ≤ (boxCount H : ℝ)

end CubicTargets.BoxHeight
