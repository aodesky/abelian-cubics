import Cubic.BoxAsymptotic.PrimaryGenerator

/-! Actual ideal characters and the ideal series `D_k`. The primary generator is
chosen in the ring of integers and proved unique in `PrimaryGenerator`. The
character is extended by zero to ideals divisible by the prime above three. -/

noncomputable section

namespace Cubic.BoxAsymptotic.AngularIdealData

open Cubic.PoissonSummation.CyclotomicIntegerUnits
open Cubic.Counting.EisensteinNormCount
open Cubic.BoxAsymptotic.AngularSeriesData
open CubicTargets.BoxAsymptotic

/-- Coordinates of an actual Eisenstein integer in the basis `1,ζ`. -/
def coordinates (x : Integers) : ℤ × ℤ := Function.surjInv coord_surjective x

@[simp] theorem coord_coordinates (x : Integers) : coord (coordinates x) = x :=
  Function.surjInv_eq coord_surjective x

@[simp] theorem coordinates_coord (p : ℤ × ℤ) : coordinates (coord p) = p :=
  coord_injective (coord_coordinates _)

/-- `ψ_k(𝔞)`, extended by zero when `𝔞` is not prime to three. -/
def psi (k : ℤ) (I : Ideal Integers) : ℂ :=
  if 3 ∣ Ideal.absNorm I then 0
  else phase k (eis (coordinates (PrimaryGenerator.generator I)))

/-- The ideals appearing in the coefficient at `M` of `D_k`. -/
def cubeNormIdeals (M : ℕ) : Set (Ideal Integers) := {I | Ideal.absNorm I = M ^ 3}

/-- The coefficient of the ideal series `D_k`; the factor at three is omitted. -/
def idealCoefficient (k : ℤ) (M : ℕ) : ℂ :=
  if 3 ∣ M then 0 else ∑ᶠ I ∈ cubeNormIdeals M, psi k I

/-- The paper's independently defined ideal series `D_k`. -/
def idealSeries (k : ℤ) (s : ℂ) : ℂ := LSeries (idealCoefficient k) s

end Cubic.BoxAsymptotic.AngularIdealData
