import Cubic.SurfaceGeometry.BoundaryLine
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.AdjoinRoot

/-! At the generic point of the boundary line, use the projective chart C=1
and its coordinate D. The A=0 hyperplane section then has coordinate algebra
Q(D)[B]/(F(0,B,1,D)). Its length computes the boundary multiplicity. -/

noncomputable section

namespace Cubic.SurfaceGeometry.BoundaryMultiplicity

open Polynomial

abbrev BoundaryField := RatFunc ℚ

def sectionPolynomial : BoundaryField[X] :=
  CubicData.F 0 X 1 (C RatFunc.X)

abbrev genericSection := BoundaryField[X] ⧸ Ideal.span {sectionPolynomial}

theorem section_equation : sectionPolynomial = X ^ 3 := by
  simp [sectionPolynomial, CubicData.F]

/-- The hyperplane A=0 has multiplicity three along its reduced boundary. -/
theorem generic_length : Module.finrank BoundaryField genericSection = 3 := by
  unfold genericSection
  rw [finrank_quotient_span_eq_natDegree, section_equation]
  simp

end Cubic.SurfaceGeometry.BoundaryMultiplicity
