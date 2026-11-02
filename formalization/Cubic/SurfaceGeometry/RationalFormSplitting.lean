import Cubic.SurfaceGeometry.RationalFormData
import Cubic.SurfaceGeometry.SurfaceCoordinateChange
import Mathlib.Tactic.FieldSimp

namespace Cubic.SurfaceGeometry.RationalFormSplitting

open RationalFormData CubicData

variable {k : Type*} [Field k] [CharZero k]

theorem splitting_equation (r : k) (hr : r ^ 2 = -3) (x : Fin 4 → k) :
    splitCubic (splitChange r x) = normCubic x := by
  simp only [splitCubic, splitChange, normCubic, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]
  linear_combination -(x 0 * x 2 ^ 2) * hr

theorem split_inverse (r : k) (hr : r ≠ 0) (x : Fin 4 → k) :
    inverseSplitChange r (splitChange r x) = x := by
  funext i
  fin_cases i <;> simp [inverseSplitChange, splitChange] <;> field_simp [hr] <;> ring

theorem inverse_split (r : k) (hr : r ≠ 0) (x : Fin 4 → k) :
    splitChange r (inverseSplitChange r x) = x := by
  funext i
  fin_cases i <;> simp [inverseSplitChange, splitChange] <;> field_simp [hr] <;> ring

theorem boundary (v : Fin 4 → k) :
    (coordinateChange v 0 = 0 ∧ coordinateChange v 3 = 0) ↔ v 0 = 0 ∧ v 1 = 0 := by
  simp only [coordinateChange, Matrix.cons_val_zero, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]
  constructor
  · rintro ⟨ha,hb⟩
    refine ⟨ha,?_⟩
    have h : (3 : k) * v 1 = 0 := by linear_combination ha - hb
    exact (mul_eq_zero.mp h).resolve_left (by norm_num)
  · rintro ⟨ha,hb⟩
    simp [ha,hb]

end Cubic.SurfaceGeometry.RationalFormSplitting
