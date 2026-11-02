import Cubic.SurfaceGeometry.CubicPresentationData
import Cubic.SurfaceGeometry.HypersurfaceDualityData

noncomputable section

namespace Cubic.SurfaceGeometry.CubicAdjunctionData

open HypersurfaceDualityData

def equation : Ambient ℚ := MvPolynomial.map (Int.castRingHom ℚ)
  CubicPresentationData.cubic

abbrev CoordinateRing := Ambient ℚ ⧸ Ideal.span {equation}

/-- The canonical module computed from the hypersurface's dual free resolution. -/
abbrev CanonicalModule := DualCohomology ℚ equation

def CanonicalDegree (n : ℤ) (x : CanonicalModule) : Prop :=
  CohomologyDegree ℚ equation 3 n x

def CoordinateDegree (n : ℤ) (x : CoordinateRing) : Prop :=
  ∃ p : Ambient ℚ, Homogeneous ℚ p n ∧ Ideal.Quotient.mk _ p = x

end Cubic.SurfaceGeometry.CubicAdjunctionData
