import Cubic.SurfaceGeometry.AffineModelData

noncomputable section

namespace Cubic.SurfaceGeometry.AffineSpecialFibre

open MvPolynomial AffineModelData

abbrev k := ZMod 3
abbrev PlaneRing := MvPolynomial (Fin 2) k

def eliminate : AffinePolynomial k →ₐ[k] PlaneRing :=
  aeval ![X 0, X 1 ^ 2 - X 0 * X 1 + X 0 ^ 3, X 1]

def includePlane : PlaneRing →ₐ[k] AffinePolynomial k := aeval ![X 0, X 2]

theorem reduced_equation : equation k = X 2 ^ 2 - X 0 * X 2 + X 0 ^ 3 - X 1 := by
  have h3 : (3 : AffinePolynomial k) = 0 := by
    simpa only [map_ofNat, map_zero] using congrArg (C : k →+* AffinePolynomial k)
      (show (3 : k) = 0 by decide)
  have h6 : (6 : AffinePolynomial k) = 0 := by linear_combination 2 * h3
  have h9 : (9 : AffinePolynomial k) = 0 := by linear_combination 3 * h3
  simp only [equation, CubicData.affineRelation, h3, h6, h9, zero_mul, add_zero]

theorem eliminate_equation : eliminate (equation k) = 0 := by
  rw [reduced_equation]
  simp [eliminate]

def forward : CoordinateRing k →ₐ[k] PlaneRing :=
  Ideal.Quotient.liftₐ _ eliminate (by
    change Ideal.span {equation k} ≤ RingHom.ker eliminate.toRingHom
    rw [Ideal.span_singleton_le_iff_mem]
    exact eliminate_equation)

def backward : PlaneRing →ₐ[k] CoordinateRing k :=
  (Ideal.Quotient.mkₐ k _).comp includePlane

theorem coordinate_b :
    coordinate k 1 = coordinate k 2 ^ 2 - coordinate k 0 * coordinate k 2 +
      coordinate k 0 ^ 3 := by
  have h : Ideal.Quotient.mk (Ideal.span {equation k}) (equation k) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have h' := (congrArg (Ideal.Quotient.mk (Ideal.span {equation k}))
    reduced_equation).symm.trans h
  simp only [map_add, map_sub, map_mul, map_pow] at h'
  exact (sub_eq_zero.mp h').symm

def presentation : CoordinateRing k ≃ₐ[k] PlaneRing :=
  AlgEquiv.ofAlgHom forward backward
    (by ext i : 1; fin_cases i <;> simp [forward, backward, eliminate, includePlane])
    (by
      apply Ideal.Quotient.algHom_ext
      ext i : 1
      fin_cases i <;> simp [forward, backward, eliminate, includePlane,
        Ideal.Quotient.mkₐ_eq_mk]
      exact coordinate_b.symm)

end Cubic.SurfaceGeometry.AffineSpecialFibre
