import Cubic.SurfaceGeometry.CubicPresentationData

noncomputable section

namespace Cubic.SurfaceGeometry.BoundaryData

open MvPolynomial CubicPresentationData

def lineIdeal : Ideal CubicRing := Ideal.span {X 0, X 1}

def hyperplaneIdeal : Ideal CubicRing := Ideal.span {cubic, X 0}

def restriction : CubicRing →ₐ[ℤ] MvPolynomial (Fin 2) ℤ := aeval ![0, 0, X 0, X 1]

def inclusion : MvPolynomial (Fin 2) ℤ →ₐ[ℤ] CubicRing := aeval ![X 2, X 3]

end Cubic.SurfaceGeometry.BoundaryData
