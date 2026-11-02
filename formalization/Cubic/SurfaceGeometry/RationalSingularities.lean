import Cubic.SurfaceGeometry.RationalFormData
import Mathlib.Tactic.FinCases

namespace Cubic.SurfaceGeometry.RationalSingularities

open MvPolynomial RationalFormData CubicData

variable {k : Type*} [Field k] [CharZero k]

theorem split_gradient (x : Fin 4 → k) (i : Fin 4) :
    eval x (pderiv i (splitCubic (fun j => X j))) =
      ![x 1 * x 2, x 0 * x 2, x 0 * x 1, -3 * x 3 ^ 2] i := by
  fin_cases i <;> simp [splitCubic] <;> ring

theorem norm_gradient (x : Fin 4 → k) (i : Fin 4) :
    eval x (pderiv i (normCubic (fun j => X j))) =
      ![x 1 ^ 2 + 3 * x 2 ^ 2, 2 * x 0 * x 1, 6 * x 0 * x 2,
        -3 * x 3 ^ 2] i := by
  have h3 (j : Fin 4) : pderiv j (3 : MvPolynomial (Fin 4) k) = 0 := by
    change pderiv j ((3 : ℕ) : MvPolynomial (Fin 4) k) = 0
    rw [← map_natCast (C : k →+* MvPolynomial (Fin 4) k), pderiv_C]
  fin_cases i <;> simp [normCubic,h3] <;> ring

theorem split_singular_locus (x : Fin 4 → k) :
    SplitSingular k x ↔ ∃ (i : Fin 3) (c : k), c ≠ 0 ∧ x = c • splitVertex i := by
  constructor
  · rintro ⟨hx,_,hg⟩
    have h3 : x 3 = 0 := by
      have h := hg 3
      rw [split_gradient] at h
      simpa using h
    have h01 : x 0 * x 1 = 0 := by simpa only [split_gradient] using hg 2
    have h02 : x 0 * x 2 = 0 := by simpa only [split_gradient] using hg 1
    have h12 : x 1 * x 2 = 0 := by simpa only [split_gradient] using hg 0
    by_cases h0 : x 0 = 0
    · by_cases h1 : x 1 = 0
      · have h2 : x 2 ≠ 0 := by
          intro h2
          apply hx
          funext i
          fin_cases i <;> simp [h0,h1,h2,h3]
        refine ⟨2,x 2,h2,?_⟩
        funext i
        fin_cases i <;> simp [splitVertex,h0,h1,h3]
      · have h2 := (mul_eq_zero.mp h12).resolve_left h1
        refine ⟨1,x 1,h1,?_⟩
        funext i
        fin_cases i <;> simp [splitVertex,h0,h2,h3]
    · have h1 := (mul_eq_zero.mp h01).resolve_left h0
      have h2 := (mul_eq_zero.mp h02).resolve_left h0
      refine ⟨0,x 0,h0,?_⟩
      funext i
      fin_cases i <;> simp [splitVertex,h1,h2,h3]
  · rintro ⟨i,c,hc,rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · intro h
      have he := congrFun h ⟨i.val,by omega⟩
      exact hc (by simpa [splitVertex] using he)
    · fin_cases i <;> simp [splitCubic,splitVertex]
    · intro j
      rw [split_gradient]
      fin_cases i <;> fin_cases j <;> simp [splitVertex]

theorem norm_singular_locus (r : k) (hr : r ^ 2 = -3) (x : Fin 4 → k) :
    NormSingular k x ↔ ∃ (i : Fin 3) (c : k), c ≠ 0 ∧ x = c • normVertex r i := by
  constructor
  · rintro ⟨hx,_,hg⟩
    have h3 : x 3 = 0 := by
      have h := hg 3
      rw [norm_gradient] at h
      simpa using h
    have hN : x 1 ^ 2 + 3 * x 2 ^ 2 = 0 := by
      simpa only [norm_gradient] using hg 0
    by_cases h0 : x 0 = 0
    · have h2 : x 2 ≠ 0 := by
        intro h2
        have h1 : x 1 = 0 := by simpa [h2] using hN
        apply hx
        funext i
        fin_cases i <;> simp [h0,h1,h2,h3]
      have hp : (x 1 - r * x 2) * (x 1 + r * x 2) = 0 := by
        linear_combination hN - x 2 ^ 2 * hr
      rcases mul_eq_zero.mp hp with hp | hp
      · refine ⟨1,x 2,h2,?_⟩
        have h1 := sub_eq_zero.mp hp
        funext i
        fin_cases i <;> simp [normVertex,h0,h3,h1,mul_comm]
      · refine ⟨2,x 2,h2,?_⟩
        have h1 : x 1 = -(r * x 2) := eq_neg_of_add_eq_zero_left hp
        funext i
        fin_cases i <;> simp [normVertex,h0,h3,h1,mul_comm]
    · have h1 : x 1 = 0 := by
        have h := hg 1
        rw [norm_gradient] at h
        simpa [h0] using h
      have h2 : x 2 = 0 := by
        have h := hg 2
        rw [norm_gradient] at h
        simpa [h0] using h
      refine ⟨0,x 0,h0,?_⟩
      funext i
      fin_cases i <;> simp [normVertex,h1,h2,h3]
  · rintro ⟨i,c,hc,rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · intro h
      fin_cases i
      · exact hc (by simpa [normVertex] using congrFun h 0)
      · exact hc (by simpa [normVertex] using congrFun h 2)
      · exact hc (by simpa [normVertex] using congrFun h 2)
    · fin_cases i <;> simp [normCubic,normVertex]
    · intro j
      rw [norm_gradient]
      fin_cases i <;> fin_cases j <;> simp [normVertex,mul_pow,hr] <;> ring

end Cubic.SurfaceGeometry.RationalSingularities
