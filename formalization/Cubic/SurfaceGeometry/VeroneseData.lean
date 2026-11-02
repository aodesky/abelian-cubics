import Cubic.SurfaceGeometry.VeroneseGrading
import Mathlib.RingTheory.Adjoin.Basic

noncomputable section

namespace Cubic.SurfaceGeometry.VeroneseData

open MvPolynomial InvariantCubicData VeroneseGrading
open Cubic.ToricHeights.TernaryCyclicInvariants

/-- The genuine degree-zero component modulo three, with its induced product. -/
def zeroComponent (w : Fin 3 → ZMod 3) : Subalgebra ℤ TernaryRing where
  carrier := {p | IsWeightedHomogeneous w p 0}
  zero_mem' := isWeightedHomogeneous_zero ℤ w 0
  one_mem' := isWeightedHomogeneous_one ℤ w
  add_mem' := fun hp hq => hp.add hq
  mul_mem' := fun hp hq => by simpa only [add_zero] using hp.mul hq
  algebraMap_mem' := isWeightedHomogeneous_C w

def symmetricVeronese : Subalgebra ℤ SymmetricCoefficients := zeroComponent symmetricWeight

def thirdVeronese : Subalgebra ℤ TernaryRing := invariants ⊓ zeroComponent ordinaryWeight

def symmetricGenerators : Set SymmetricCoefficients :=
  {X 0 ^ 3, X 0 * X 1, X 2, X 1 ^ 3}

def cubicGenerators : Set TernaryRing := {A, B, InvariantCubicData.C, D}

end Cubic.SurfaceGeometry.VeroneseData
