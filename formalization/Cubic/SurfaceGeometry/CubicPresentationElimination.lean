import Cubic.SurfaceGeometry.CubicPresentationData
import Cubic.SurfaceGeometry.VeronesePresentationRelations
import Cubic.SurfaceGeometry.SurfaceIntegralEquation

noncomputable section

namespace Cubic.SurfaceGeometry.CubicPresentationElimination

open MvPolynomial InvariantCubicData VeronesePresentationData CubicPresentationData

theorem evaluation_embed (p : CubicRing) : evaluation (embed p) = cubicEvaluation p := by
  have h : evaluation.comp embed = cubicEvaluation := by
    ext i : 1
    fin_cases i <;> simp [evaluation, embed, cubicEvaluation,
      coefficientEvaluation, symmetricEval, SymmetricVeroneseRelations.substitution,
      A, B, InvariantCubicData.C, D]
  exact DFunLike.congr_fun h p

theorem eliminate_embed (p : CubicRing) : eliminate (embed p) = p := by
  have h : eliminate.comp embed = AlgHom.id ℤ CubicRing := by
    ext i : 1
    fin_cases i <;> simp [eliminate, embed, eliminateCoefficients]
  exact DFunLike.congr_fun h p

theorem eliminate_C (a : Coefficients) :
    eliminate (Polynomial.C a) = eliminateCoefficients a := Polynomial.eval₂_C _ _

theorem eliminate_X : eliminate Polynomial.X = X 3 := Polynomial.eval₂_X _ _

theorem eliminateCoefficients_X (i : Fin 4) :
    eliminateCoefficients (X i) = ![X 1, X 0, hExpression, X 2] i := by
  simp only [eliminateCoefficients, aeval_X]

theorem eliminate_quadratic : eliminate quadratic = 0 := by
  simp only [quadratic, map_add, map_sub, map_mul, map_pow, map_ofNat,
    eliminate_C, eliminate_X, eliminateCoefficients_X]
  dsimp [hExpression]
  ring

theorem eliminate_symmetricRelation : eliminate symmetricRelation = cubic := by
  simp only [symmetricRelation, SymmetricVeroneseRelations.multivariateRelation,
    map_sub, map_mul, map_pow, eliminate_C, eliminateCoefficients_X]
  dsimp [hExpression, cubic, CubicData.F]
  ring

theorem cubic_root : cubicEvaluation cubic = 0 := by
  have hx (i : Fin 4) : cubicEvaluation (X i) = ![A, B, InvariantCubicData.C, D] i := by
    simp only [cubicEvaluation, aeval_X]
  simp only [cubic, CubicData.F, map_add, map_sub, map_mul, map_pow, map_ofNat, hx]
  exact SurfaceIntegralEquation.«eqn:surfaceIntegralCubic»

theorem kernel : RingHom.ker cubicEvaluation.toRingHom = Ideal.span {cubic} := by
  apply le_antisymm
  · intro p hp
    have hpe : embed p ∈ relations := by
      rw [← VeronesePresentationRelations.kernel]
      change evaluation (embed p) = 0
      rw [evaluation_embed]
      exact hp
    have he : relations ≤ Ideal.comap eliminate.toRingHom (Ideal.span {cubic}) := by
      rw [relations, Ideal.span_le]
      intro q hq
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
      rcases hq with rfl | rfl
      · change eliminate symmetricRelation ∈ Ideal.span {cubic}
        rw [eliminate_symmetricRelation]
        exact Ideal.subset_span (Set.mem_singleton _)
      · change eliminate quadratic ∈ Ideal.span {cubic}
        rw [eliminate_quadratic]
        exact Ideal.zero_mem _
    have hp' := he hpe
    change eliminate (embed p) ∈ Ideal.span {cubic} at hp'
    rwa [eliminate_embed] at hp'
  · rw [Ideal.span_le]
    rintro p rfl
    exact cubic_root

end Cubic.SurfaceGeometry.CubicPresentationElimination
