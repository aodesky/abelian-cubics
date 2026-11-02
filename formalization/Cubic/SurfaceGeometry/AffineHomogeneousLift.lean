import Cubic.SurfaceGeometry.AffineDehomogenization
import Cubic.SurfaceGeometry.CubicGrading
import Cubic.ToricHeights.AffineC3Invariants

noncomputable section

namespace Cubic.SurfaceGeometry.AffineHomogeneousLift

open MvPolynomial AffineModelData CubicPresentationData
open Cubic.ToricHeights

theorem dehomogenize_homogenize (p : AffinePolynomial ℤ) :
    dehomogenize (homogenizeCoordinates p) = p := by
  have h : dehomogenize.comp homogenizeCoordinates = AlgHom.id ℤ _ := by
    ext i : 1
    fin_cases i <;> simp [dehomogenize, homogenizeCoordinates]
  exact DFunLike.congr_fun h p

theorem exists_homogeneous_lift (p : AffinePolynomial ℤ) :
    ∃ (n : ℕ) (q : CubicRing), q.IsHomogeneous n ∧ dehomogenize q = p := by
  let q := homogenizeCoordinates p
  refine ⟨q.totalDegree, ∑ d ∈ Finset.range (q.totalDegree + 1),
    homogeneousComponent d q * X 0 ^ (q.totalDegree - d), ?_, ?_⟩
  · apply IsHomogeneous.sum
    intro d hd
    have hd' : d ≤ q.totalDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)
    have h := (homogeneousComponent_isHomogeneous d q).mul
      ((isHomogeneous_X ℤ 0).pow (q.totalDegree - d))
    rwa [one_mul, Nat.add_sub_cancel' hd'] at h
  · simp only [map_sum, map_mul, map_pow, AffineDehomogenization.dehomogenize_X,
      Matrix.cons_val_zero, one_pow, mul_one]
    rw [← map_sum, sum_homogeneousComponent]
    exact dehomogenize_homogenize p

theorem invariant_evaluation (p : CubicRing) :
    ChartDehomogenization.dehom (cubicEvaluation p) =
      invariantEvaluation (dehomogenize p) := by
  have h : ChartDehomogenization.dehom.comp cubicEvaluation =
      invariantEvaluation.comp dehomogenize := by
    ext i : 1
    fin_cases i <;>
      simp [cubicEvaluation, invariantEvaluation, dehomogenize,
        InvariantCubicData.A, InvariantCubicData.B, InvariantCubicData.C,
        InvariantCubicData.D, AffineC3Invariants.esymm_one, AffineC3Invariants.esymm_two,
        AffineC3Invariants.esymm_three, TernaryCyclicInvariants.delta,
        AffineChartInvariants.e2, AffineChartInvariants.e3, AffineChartInvariants.delta,
        AffineInvariantRing.linearPolynomial, AffineInvariantRing.thirdCoordinate,
        Fin.sum_univ_three] <;> ring
  exact DFunLike.congr_fun h p

end Cubic.SurfaceGeometry.AffineHomogeneousLift
