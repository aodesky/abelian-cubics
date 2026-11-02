import Cubic.SurfaceGeometry.AffineModelData
import Mathlib.Tactic.FinCases

noncomputable section

namespace Cubic.SurfaceGeometry.SpecialFibreSingularities

open MvPolynomial AffineModelData

theorem gradient {k : Type*} [Field k] (x : Fin 4 → k) (i : Fin 4) :
    eval x (pderiv i (CubicData.F (X 0) (X 1) (X 2) (X 3))) =
      ![x 3 ^ 2 - x 1 * x 3 + 3 * x 2 * x 3 + 2 * x 0 * x 2 -
          6 * x 1 * x 2 + 9 * x 2 ^ 2,
        3 * x 1 ^ 2 - x 0 * x 3 - 6 * x 0 * x 2,
        3 * x 0 * x 3 + x 0 ^ 2 - 6 * x 0 * x 1 + 18 * x 0 * x 2,
        2 * x 0 * x 3 - x 0 * x 1 + 3 * x 0 * x 2] i := by
  have hn (j : Fin 4) (n : ℕ) :
      pderiv j (n : MvPolynomial (Fin 4) k) = 0 := by
    rw [← map_natCast (C : k →+* MvPolynomial (Fin 4) k), pderiv_C]
  have h3 (j : Fin 4) : pderiv j (3 : MvPolynomial (Fin 4) k) = 0 := hn j 3
  have h6 (j : Fin 4) : pderiv j (6 : MvPolynomial (Fin 4) k) = 0 := hn j 6
  have h9 (j : Fin 4) : pderiv j (9 : MvPolynomial (Fin 4) k) = 0 := hn j 9
  fin_cases i <;>
    simp [CubicData.F, pderiv_mul, pderiv_pow, Pi.single_apply, h3, h6, h9] <;> ring

theorem singular_locus (k : Type*) [Field k] [CharP k 3] (x : Fin 4 → k) :
    Singular k x ↔ ∃ c : k, c ≠ 0 ∧ x = ![0, 0, c, 0] := by
  have h3 : (3 : k) = 0 := CharP.cast_eq_zero k 3
  have h6 : (6 : k) = 0 := by linear_combination 2 * h3
  have h9 : (9 : k) = 0 := by linear_combination 3 * h3
  have h18 : (18 : k) = 0 := by linear_combination 6 * h3
  constructor
  · rintro ⟨hx,hF,hg⟩
    have hA : x 0 = 0 := by
      have h := hg 2
      rw [gradient] at h
      simp [h3,h6,h18] at h
      exact h
    have hB : x 1 = 0 := by
      simp [CubicData.F,hA] at hF
      exact hF
    have hD : x 3 = 0 := by
      have h := hg 0
      rw [gradient] at h
      simp [hA,hB,h3,h9] at h
      exact h
    have hC : x 2 ≠ 0 := by
      intro h
      apply hx
      funext i
      fin_cases i <;> simp [hA,hB,h,hD]
    refine ⟨x 2,hC,?_⟩
    funext i
    fin_cases i <;> simp [hA,hB,hD]
  · rintro ⟨c,hc,rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · intro h
      have he := congrFun h 2
      exact hc (by simpa using he)
    · simp [CubicData.F]
    · intro i
      rw [gradient]
      fin_cases i <;> simp [h3,h6,h9,h18]

end Cubic.SurfaceGeometry.SpecialFibreSingularities
