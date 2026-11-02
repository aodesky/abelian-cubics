import Cubic.SurfaceGeometry.VeroneseData
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Localization.FractionRing

/-! Standard projective chart functions, represented in the fraction field of
the original invariant ring. The degree condition is imposed on the original
polynomial numerator, before passing to the third Veronese. -/

noncomputable section

namespace Cubic.SurfaceGeometry.ProjectiveChartData

open Cubic.ToricHeights.TernaryCyclicInvariants

abbrev InvariantFractionField := FractionRing invariants

def fraction (p f : invariants) (n : ℕ) : InvariantFractionField :=
  algebraMap invariants _ p / algebraMap invariants _ f ^ n

/-- Functions on D₊(f), where f is homogeneous of degree d. -/
def Chart (f : invariants) (d : ℕ) : Set InvariantFractionField :=
  {x | ∃ n : ℕ, ∃ p : invariants,
    p.val.IsHomogeneous (d * n) ∧ fraction p f n = x}

/-- Functions on D₊(f³) in the third Veronese. Both numerator and
denominator have degree 3dn in the original grading. -/
def VeroneseChart (f : invariants) (d : ℕ) : Set InvariantFractionField :=
  {x | ∃ n : ℕ, ∃ p : VeroneseData.thirdVeronese,
    p.val.IsHomogeneous (3 * (d * n)) ∧
      fraction ⟨p.val, p.property.1⟩ (f ^ 3) n = x}

end Cubic.SurfaceGeometry.ProjectiveChartData
