import Cubic.SurfaceGeometry.CubicAdjunctionData
import Cubic.SurfaceGeometry.HypersurfaceDuality
import Cubic.SurfaceGeometry.CubicGrading

noncomputable section

namespace Cubic.SurfaceGeometry.CubicAdjunction

open MvPolynomial HypersurfaceDualityData HypersurfaceDuality CubicAdjunctionData

theorem integer_homogeneous {k : Type*} [Field k] {p : Ambient k} {n : ℕ}
    (hp : p.IsHomogeneous n) : Homogeneous k p (n : ℤ) := by
  intro d hd
  have he := congrArg (fun m : ℕ => (m : ℤ)) (hp hd)
  simpa [Finsupp.weight_apply, Finsupp.sum] using he

theorem equation_homogeneous : Homogeneous ℚ equation 3 :=
  integer_homogeneous (CubicGrading.cubic_homogeneous.map (Int.castRingHom ℚ))

theorem equation_ne_zero : equation ≠ 0 := by
  intro he
  have h := congrArg (MvPolynomial.eval (![0,1,0,0] : Fin 4 → ℚ)) he
  norm_num [equation, CubicPresentationData.cubic, CubicData.F] at h

theorem free_resolution_exact :
    Function.Injective (multiplication ℚ equation) ∧
    LinearMap.range (multiplication ℚ equation) =
      LinearMap.ker (Ideal.span {equation}).mkQ :=
  resolution_exact ℚ equation_ne_zero

def adjunction : CanonicalModule ≃ₗ[Ambient ℚ] CoordinateRing :=
  cokernelEquiv ℚ equation

/-- In degree n the canonical module is the coordinate ring in degree n−1:
the hypersurface adjunction computation gives the twist O(-1). -/
theorem adjunction_degree (n : ℤ) (x : CanonicalModule) :
    CanonicalDegree n x ↔ CoordinateDegree (n - 1) (adjunction x) := by
  have he := cohomology_degree_iff ℚ equation 3 n x
  simpa only [CanonicalDegree, CoordinateDegree, adjunction,
    show (3 : ℤ) + n - 4 = n - 1 by omega] using he

end Cubic.SurfaceGeometry.CubicAdjunction
