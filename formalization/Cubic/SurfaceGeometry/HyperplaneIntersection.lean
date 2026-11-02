import Cubic.SurfaceGeometry.HyperplaneIntersectionData
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Ring

noncomputable section

namespace Cubic.SurfaceGeometry.HyperplaneIntersection

open Polynomial HyperplaneIntersectionData

theorem infinity_ne_zero : infinityValue ≠ 0 := by
  let p : Parameters := 1 + MvPolynomial.X 1 * MvPolynomial.X 3 ^ 2 -
    MvPolynomial.X 1 * MvPolynomial.X 3
  have hp : p ≠ 0 := by
    intro he
    have h := congrArg (MvPolynomial.eval (fun _ => (0 : ℚ))) he
    norm_num [p] at h
  have he : algebraMap Parameters ParameterField p = infinityValue := by
    simp [p, infinityValue, parameter, CubicData.F]
  rw [← he]
  exact fun h => hp ((IsFractionRing.injective Parameters ParameterField)
    (h.trans (map_zero _).symm))

theorem leading_coefficient : sectionPolynomial.coeff 3 = infinityValue := by
  unfold sectionPolynomial infinityValue CubicData.F
  compute_degree!

theorem degree_bound : sectionPolynomial.natDegree ≤ 3 := by
  unfold sectionPolynomial CubicData.F
  compute_degree!

theorem degree : sectionPolynomial.natDegree = 3 :=
  natDegree_eq_of_le_of_coeff_ne_zero degree_bound
    (leading_coefficient ▸ infinity_ne_zero)

/-- There is no intersection at C=0, and the affine generic intersection
has length three. Thus the actual hyperplane class has square three. -/
theorem generic_length : Module.finrank ParameterField IntersectionRing = 3 := by
  rw [finrank_quotient_span_eq_natDegree, degree]

end Cubic.SurfaceGeometry.HyperplaneIntersection
