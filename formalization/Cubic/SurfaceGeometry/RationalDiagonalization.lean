import Cubic.SurfaceGeometry.DiagonalCubicData
import Cubic.ToricHeights.AffinePointParameter

namespace Cubic.SurfaceGeometry.RationalDiagonalization

open DiagonalCubicData RationalFormData CubicData
open Cubic.QuadraticCorrespondence.CyclotomicField
open Cubic.ToricHeights

theorem diagonal_action (x : Fin 3 → E) :
    linearForms ![x 1,x 2,x 0] =
      ![linearForms x 0,zeta^2*linearForms x 1,zeta*linearForms x 2] := by
  have hs : zeta^2 = -1-zeta := by linear_combination zeta_relation
  funext i
  fin_cases i <;> simp [linearForms,hs] <;>
    ring_nf <;> simp only [hs] <;> ring

theorem inverse_linear (x : Fin 3 → E) : inverseLinearForms (linearForms x) = x := by
  have hs : zeta^2 = -1-zeta := by linear_combination zeta_relation
  funext i
  fin_cases i <;> simp [linearForms,inverseLinearForms,hs] <;>
    ring_nf <;> simp only [hs] <;> ring

theorem linear_inverse (x : Fin 3 → E) : linearForms (inverseLinearForms x) = x := by
  have hs : zeta^2 = -1-zeta := by linear_combination zeta_relation
  funext i
  fin_cases i <;> simp [linearForms,inverseLinearForms,hs] <;>
    ring_nf <;> simp only [hs] <;> ring

theorem cubics_coordinate_change (x : Fin 3 → E) :
    splitChange sqrtNegThree (coordinateChange (originalCubics x)) =
      diagonalCubics (linearForms x) := by
  have hp := TraceOneCharacters.eigenvalue_product zeta zeta_relation (x 0) (x 1) (x 2)
  have hs := TraceOneCharacters.eigenvalue_cubes_sum zeta zeta_relation (x 0) (x 1) (x 2)
  have hd := AffinePointParameter.eigenvalue_delta zeta (x 0) (x 1) (x 2) zeta_relation
  simp only [Cubic.OrbitParametrization.secondCoeff,Cubic.OrbitParametrization.constantCoeff] at hp hs hd
  funext i
  fin_cases i <;> simp [splitChange,coordinateChange,originalCubics,diagonalCubics,linearForms]
  · simp only [sqrtNegThree]
    linear_combination -hs/2-hd/2
  · simp only [sqrtNegThree]
    linear_combination -hs/2+hd/2
  · linear_combination -(x 0+x 1+x 2)*hp

theorem conjugate_linear (x : Fin 3 → E) :
    linearForms (fun i => conjugation (x i)) =
      ![conjugation (linearForms x 0),conjugation (linearForms x 2),
        conjugation (linearForms x 1)] := by
  have h4 := TraceOneCharacters.root_fourth zeta zeta_relation
  funext i
  fin_cases i <;> simp [linearForms,conjugation_zeta_sq,← pow_mul,h4]

/-- The two conditions in the proof, before reducing exponents. -/
theorem invariant_exponents (a b c : ℕ) :
    (3 ∣ a+b+c ∧ 3 ∣ 2*b+c) ↔ a%3=b%3 ∧ b%3=c%3 := by omega

end Cubic.SurfaceGeometry.RationalDiagonalization
