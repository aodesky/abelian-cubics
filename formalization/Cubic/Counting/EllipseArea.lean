import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# The area of the filled ellipse `E_H°`

Lemmas for `eqn:ellipseLatticeCount`. Following the proof of
`lemma:reducibles`, put `u = x - 1/3`, `v = y - 1/3`; the region becomes
`u² + uv + v² ≤ H²/3`, and the linear map `(u, v) ↦ (u + v/2, √3 v/2)`,
of determinant `√3/2`, sends it onto the disk of radius `H/√3`. We realize the
target plane as `ℂ`, so that this disk is `Metric.closedBall 0 (H/√3)`.
-/

namespace Cubic.Counting.EllipseArea

open MeasureTheory Real

/-- The quadratic polynomial `x² + y² + xy - x - y` defining the ellipse `E_H`. -/
def ellipseForm (p : ℝ × ℝ) : ℝ := p.1 ^ 2 + p.2 ^ 2 + p.1 * p.2 - p.1 - p.2

/-- The closed region `E_h°` bounded by `E_h`. -/
def region (h : ℝ) : Set (ℝ × ℝ) := {p | ellipseForm p ≤ (h ^ 2 - 1) / 3}

/-- The linear change of variables `(u, v) ↦ (u + v/2, √3 v/2)`. -/
noncomputable def shear : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ where
  toFun p := (p.1 + p.2 / 2, √3 / 2 * p.2)
  map_add' p q := by ext <;> simp <;> ring
  map_smul' c p := by ext <;> simp <;> ring

theorem det_shear : LinearMap.det shear = √3 / 2 := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, shear]

/-- The composite of the translation by `-(1/3, 1/3)`, `shear`, and the
identification `ℝ × ℝ ≃ ℂ`. -/
noncomputable def ψ (p : ℝ × ℝ) : ℂ :=
  ⟨(p.1 - 1 / 3) + (p.2 - 1 / 3) / 2, √3 / 2 * (p.2 - 1 / 3)⟩

theorem sq_norm_ψ (p : ℝ × ℝ) : ‖ψ p‖ ^ 2 = ellipseForm p + 1 / 3 := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [ψ, ellipseForm]
  linear_combination ((p.2 - 1 / 3) ^ 2 / 4) * h3

theorem ψ_sub (z w : ℝ × ℝ) :
    ψ z - ψ w = ⟨(z.1 - w.1) + (z.2 - w.2) / 2, √3 / 2 * (z.2 - w.2)⟩ := by
  apply Complex.ext <;> simp [ψ] <;> ring

/-- For `h ≥ 0`, membership in `E_h°` is the disk condition `‖ψ p‖ ≤ h/√3`. -/
theorem mem_region_iff {h : ℝ} (hh : 0 ≤ h) (p : ℝ × ℝ) :
    p ∈ region h ↔ ‖ψ p‖ ≤ h / √3 := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < √3 := by positivity
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), sq_norm_ψ, div_pow, h3]
  simp only [region, Set.mem_setOf_eq]
  constructor <;> intro h <;> linarith

theorem region_eq_preimage {h : ℝ} (hh : 0 ≤ h) :
    region h = (fun p : ℝ × ℝ => p + (-(1 / 3 : ℝ), -(1 / 3 : ℝ))) ⁻¹'
      (shear ⁻¹' (Complex.measurableEquivRealProd.symm ⁻¹'
        Metric.closedBall 0 (h / √3))) := by
  ext p
  rw [mem_region_iff hh]
  simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
  have : Complex.measurableEquivRealProd.symm (shear (p + (-(1 / 3 : ℝ), -(1 / 3 : ℝ)))) =
      ψ p := by
    apply Complex.ext <;> simp [shear, ψ] <;> ring
  rw [this]

/-- The area of `E_h°` is `2π h² / (3√3)` for `h ≥ 0`. -/
theorem volume_region {h : ℝ} (hh : 0 ≤ h) :
    volume (region h) = ENNReal.ofReal (2 * π / (3 * √3) * h ^ 2) := by
  have hpos : 0 < √3 := by positivity
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hdet : LinearMap.det shear ≠ 0 := by rw [det_shear]; positivity
  rw [region_eq_preimage hh, measure_preimage_add_right,
    MeasureTheory.Measure.addHaar_preimage_linearMap _ hdet,
    (Complex.volume_preserving_equiv_real_prod.symm _).measure_preimage
      measurableSet_closedBall.nullMeasurableSet,
    Complex.volume_closedBall, det_shear, ← ENNReal.ofReal_pow (by positivity),
    ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [abs_of_pos (by positivity)]
  field_simp
  rw [h3]
  ring

end Cubic.Counting.EllipseArea
