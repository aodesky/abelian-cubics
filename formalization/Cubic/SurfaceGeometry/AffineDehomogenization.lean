import Cubic.SurfaceGeometry.AffineModelData

noncomputable section

namespace Cubic.SurfaceGeometry.AffineDehomogenization

open MvPolynomial CubicPresentationData AffineModelData

theorem dehomogenize_X (i : Fin 4) : dehomogenize (X i) = ![1, X 0, -X 1, X 2] i := by
  simp only [dehomogenize, aeval_X]

theorem homogenizeCoordinates_X (i : Fin 3) :
    homogenizeCoordinates (X i) = ![X 1, -X 2, X 3] i := by
  simp only [homogenizeCoordinates, aeval_X]

theorem equation_dehomogenize : dehomogenize cubic = equation ℤ := by
  simp only [cubic, equation, CubicData.F, CubicData.affineRelation,
    map_add, map_sub, map_mul, map_pow, map_ofNat, dehomogenize_X]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  ring

def forward : (CubicRing ⧸ normalizedChartIdeal) →ₐ[ℤ] CoordinateRing ℤ :=
  Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ ℤ _).comp dehomogenize) (by
    change normalizedChartIdeal ≤ RingHom.ker
      (((Ideal.Quotient.mkₐ ℤ _).comp dehomogenize).toRingHom)
    rw [normalizedChartIdeal, Ideal.span_le]
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl
    · change Ideal.Quotient.mk _ (dehomogenize cubic) = 0
      rw [equation_dehomogenize]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    · change Ideal.Quotient.mk _ (dehomogenize (X 0 - 1)) = 0
      simp [dehomogenize])

theorem normalized_A : Ideal.Quotient.mk normalizedChartIdeal (X 0) = 1 := by
  apply sub_eq_zero.mp
  rw [← map_one (Ideal.Quotient.mk normalizedChartIdeal), ← map_sub]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

theorem homogenized_relation :
    Ideal.Quotient.mk normalizedChartIdeal (homogenizeCoordinates (equation ℤ)) = 0 := by
  have hf : Ideal.Quotient.mk normalizedChartIdeal cubic = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  simp only [cubic, CubicData.F, map_add, map_sub, map_mul, map_pow, map_ofNat,
    normalized_A, one_mul, one_pow] at hf
  simp only [equation, CubicData.affineRelation, map_add, map_sub, map_mul,
    map_pow, map_ofNat, homogenizeCoordinates_X, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, map_neg]
  linear_combination hf

def backward : CoordinateRing ℤ →ₐ[ℤ] (CubicRing ⧸ normalizedChartIdeal) :=
  Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ ℤ _).comp homogenizeCoordinates) (by
    change Ideal.span {equation ℤ} ≤ RingHom.ker
      (((Ideal.Quotient.mkₐ ℤ _).comp homogenizeCoordinates).toRingHom)
    rw [Ideal.span_singleton_le_iff_mem]
    exact homogenized_relation)

def presentation : (CubicRing ⧸ normalizedChartIdeal) ≃ₐ[ℤ] CoordinateRing ℤ :=
  AlgEquiv.ofAlgHom forward backward
    (by
      apply Ideal.Quotient.algHom_ext
      ext i : 1
      fin_cases i <;> simp [forward, backward, dehomogenize, homogenizeCoordinates])
    (by
      apply Ideal.Quotient.algHom_ext
      ext i : 1
      fin_cases i <;> simp [forward, backward, dehomogenize, homogenizeCoordinates,
        Ideal.Quotient.mkₐ_eq_mk, normalized_A])

theorem presentation_mk (p : CubicRing) :
    presentation (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (dehomogenize p) := rfl

end Cubic.SurfaceGeometry.AffineDehomogenization
