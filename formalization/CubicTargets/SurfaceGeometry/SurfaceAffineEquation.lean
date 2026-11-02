import Cubic.SurfaceGeometry.AffineModelData

namespace CubicTargets.SurfaceGeometry.SurfaceAffineEquation

open Cubic.SurfaceGeometry.AffineModelData Cubic.SurfaceGeometry.CubicPresentationData

def Claim : Prop := dehomogenize cubic = equation ℤ ∧
  ∃ e : (CubicRing ⧸ normalizedChartIdeal) ≃ₐ[ℤ] CoordinateRing ℤ,
    ∀ p, e (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (dehomogenize p)

end CubicTargets.SurfaceGeometry.SurfaceAffineEquation
