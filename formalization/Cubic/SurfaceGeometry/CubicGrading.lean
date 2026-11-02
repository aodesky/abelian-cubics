import Cubic.SurfaceGeometry.CubicPresentation
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! The cubic presentation respects the actual natural-number grading: degree
`n` in A,B,C,D is degree `3n` in X,Y,Z. Every homogeneous invariant of that
degree has a homogeneous preimage, not merely an ungraded preimage. -/

noncomputable section

namespace Cubic.SurfaceGeometry.CubicGrading

open MvPolynomial InvariantCubicData CubicPresentationData VeroneseData
open Cubic.ToricHeights.TernaryCyclicInvariants

theorem e_one_homogeneous : (e 1).IsHomogeneous 1 := by
  rw [Cubic.ToricHeights.AffineC3Invariants.esymm_one]
  exact ((isHomogeneous_X ℤ 0).add (isHomogeneous_X ℤ 1)).add (isHomogeneous_X ℤ 2)

theorem e_two_homogeneous : (e 2).IsHomogeneous 2 := by
  rw [Cubic.ToricHeights.AffineC3Invariants.esymm_two]
  have hx (i : Fin 3) := isHomogeneous_X ℤ i
  exact (((hx 0).mul (hx 1)).add ((hx 0).mul (hx 2))).add ((hx 1).mul (hx 2))

theorem e_three_homogeneous : (e 3).IsHomogeneous 3 := by
  rw [Cubic.ToricHeights.AffineC3Invariants.esymm_three]
  exact ((isHomogeneous_X ℤ 0).mul (isHomogeneous_X ℤ 1)).mul (isHomogeneous_X ℤ 2)

theorem delta_homogeneous : delta.IsHomogeneous 3 := by
  unfold delta
  have hx (i : Fin 3) := isHomogeneous_X ℤ i
  exact ((((hx 0).pow 2).mul (hx 1)).add (((hx 1).pow 2).mul (hx 2))).add
    (((hx 2).pow 2).mul (hx 0))

theorem generators_homogeneous (i : Fin 4) :
    (![A, B, InvariantCubicData.C, D] i).IsHomogeneous 3 := by
  fin_cases i
  · exact e_one_homogeneous.pow 3
  · exact e_one_homogeneous.mul e_two_homogeneous
  · exact e_three_homogeneous
  · exact delta_homogeneous

theorem evaluation_homogeneous {p : CubicRing} {n : ℕ} (hp : p.IsHomogeneous n) :
    (cubicEvaluation p).IsHomogeneous (3 * n) :=
  hp.aeval _ generators_homogeneous

theorem component_evaluation (n : ℕ) (p : CubicRing) :
    homogeneousComponent (3 * n) (cubicEvaluation p) =
      cubicEvaluation (homogeneousComponent n p) := by
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial d r =>
    rw [homogeneousComponent_of_mem (evaluation_homogeneous (isHomogeneous_monomial r rfl)),
      homogeneousComponent_of_mem (isHomogeneous_monomial r rfl)]
    have he : 3 * n = 3 * d.degree ↔ n = d.degree := by omega
    simp only [he]
    split_ifs <;> simp

theorem homogeneous_preimage (n : ℕ) (f : thirdVeronese)
    (hf : f.val.IsHomogeneous (3 * n)) :
    ∃ p : CubicRing, p.IsHomogeneous n ∧ cubicEvaluation p = f.val := by
  obtain ⟨p,hp⟩ := CubicPresentation.evaluation_surjective f
  refine ⟨homogeneousComponent n p, homogeneousComponent_isHomogeneous n p, ?_⟩
  rw [← component_evaluation]
  have he : cubicEvaluation p = f.val := congrArg Subtype.val hp
  rw [he]
  exact hf.weightedHomogeneousComponent_same

theorem cubic_homogeneous : cubic.IsHomogeneous 3 := by
  have hx (i : Fin 4) := isHomogeneous_X ℤ i
  have h := (((((((hx 1).pow 3).add ((hx 0).mul ((hx 3).pow 2))).sub
    (((hx 0).mul (hx 1)).mul (hx 3))).add
    ((((hx 0).mul (hx 2)).mul (hx 3)).C_mul 3)).add
    (((hx 0).pow 2).mul (hx 2))).sub
    ((((hx 0).mul (hx 1)).mul (hx 2)).C_mul 6)).add
    (((hx 0).mul ((hx 2).pow 2)).C_mul 9)
  convert h using 1
  simp only [cubic, CubicData.F, map_ofNat]
  ring

theorem cubic_ne_zero : cubic ≠ 0 := by
  intro he
  have h := congrArg (MvPolynomial.eval (![0,1,0,0] : Fin 4 → ℤ)) he
  norm_num [cubic, CubicData.F] at h

theorem cubic_degree : cubic.totalDegree = 3 :=
  cubic_homogeneous.totalDegree cubic_ne_zero

end Cubic.SurfaceGeometry.CubicGrading
