import Cubic.AllGaloisCounts.SliceUniformBounds
import Cubic.AllGaloisCounts.TrapezoidalEstimate

/-! Smooth cells and the finitely many cells meeting a slice junction. -/

noncomputable section

namespace Cubic.AllGaloisCounts.SliceCellEstimate
open CountData LinearFactorSlice SliceThresholds SlicePieces MeasureTheory

def error (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  (b - a) / 2 * (f a + f b) - ∫ x in a..b, f x

theorem error_congr {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (he : Set.EqOn f g (Set.Icc a b)) : error f a b = error g a b := by
  unfold error
  rw [he ⟨le_rfl, hab⟩, he ⟨hab, le_rfl⟩]
  congr 1
  apply intervalIntegral.integral_congr
  simpa only [Set.uIcc_of_le hab] using he

theorem constant_error (c a b : ℝ) : error (fun _ => c) a b = 0 := by
  simp only [error, intervalIntegral.integral_const, smul_eq_mul]
  ring

theorem error_reflect (y a b : ℝ) :
    error (fun x => F x y) a b = error (fun x => F x (-y)) (-b) (-a) := by
  have hi : (∫ x in a..b, F x y) = ∫ x in -b..-a, F x (-y) := by
    simpa only [reflect, neg_neg] using
      (intervalIntegral.integral_comp_neg (f := fun x => F x (-y)) (a := a) (b := b))
  simp only [error, reflect, neg_neg]
  rw [hi]
  ring

theorem positive_cell {y a b : ℝ} (hy : y ∈ Set.Icc (-1) 1) (hab : a < b)
    (ha : minus y ≤ a) (hb : b ≤ plus y) :
    |error (fun x => F x y) a b| ≤ 2 * (b - a) ^ 3 := by
  have hx (x : ℝ) (h : x ∈ Set.Icc a b) : x ∈ Set.Icc (1 / 2) 2 :=
    ⟨SliceUniformBounds.half_le_theta_inv.trans ((bounds hy).1.trans (ha.trans h.1)),
      h.2.trans (hb.trans ((bounds hy).2.2.2.trans vartheta_spec.2.1.le))⟩
  have hp (x : ℝ) (h : x ∈ Set.Icc a b) : 0 < x := by linarith [(hx x h).1]
  rw [error_congr hab.le (show Set.EqOn (fun x => F x y) (fun x => psi x y)
    (Set.Icc a b) from fun x h => middle hy (ha.trans h.1) (h.2.trans hb))]
  have h := TrapezoidalEstimate.smooth_cell hab (by norm_num : (0 : ℝ) ≤ 18)
    (fun x h => psi_deriv (hp x h) y)
    (fun x h => SliceUniformBounds.second_derivative (hp x h) y)
    (show ContinuousOn (fun x : ℝ => 2 * x⁻¹ ^ 3 - 2) (Set.Icc a b) by
      intro x h
      exact (show ContinuousAt (fun x : ℝ => 2 * x⁻¹ ^ 3 - 2) x by
        fun_prop (disch := exact (hp x h).ne')).continuousWithinAt)
    (fun x h => SliceUniformBounds.second_derivative_bound (hx x h))
  change |error (fun x => psi x y) a b| ≤ _ at h
  nlinarith [pow_nonneg (sub_nonneg.mpr hab.le) 3]

theorem negative_cell {y a b : ℝ} (hy : y ∈ Set.Icc (-1) 1) (hab : a < b)
    (ha : -plus (-y) ≤ a) (hb : b ≤ -minus (-y)) :
    |error (fun x => F x y) a b| ≤ 2 * (b - a) ^ 3 := by
  rw [error_reflect]
  convert positive_cell (neg_parameter hy) (show -b < -a by linarith)
    (show minus (-y) ≤ -b by linarith) (show -a ≤ plus (-y) by linarith) using 1 <;> ring

def junctions (y : ℝ) : Finset ℝ := {-plus (-y), -minus (-y), minus y, plus y}

theorem junctions_card (y : ℝ) : (junctions y).card ≤ 4 := by
  classical
  unfold junctions
  have h1 := Finset.card_insert_le (-plus (-y)) {-minus (-y), minus y, plus y}
  have h2 := Finset.card_insert_le (-minus (-y)) {minus y, plus y}
  have h3 := Finset.card_insert_le (minus y) {plus y}
  simp only [Finset.card_singleton] at h3
  omega

theorem smooth_cell {y a b : ℝ} (hy : y ∈ Set.Icc (-1) 1) (hab : a < b)
    (hj : ∀ t ∈ junctions y, t ∉ Set.Icc a b) :
    |error (fun x => F x y) a b| ≤ 2 * (b - a) ^ 3 := by
  have hz : (0 : ℝ) ≤ 2 * (b - a) ^ 3 := by
    have := sub_pos.mpr hab
    positivity
  have hconstant (c : ℝ) (he : ∀ x ∈ Set.Icc a b, F x y = c) :
      |error (fun x => F x y) a b| ≤ 2 * (b - a) ^ 3 := by
    rw [error_congr hab.le he, constant_error, abs_zero]
    exact hz
  by_cases h1 : b ≤ -plus (-y)
  · apply hconstant 0
    intro x hx
    rw [← neg_neg x, reflect]
    apply after (neg_parameter hy)
    linarith [hx.2]
  have h1' : -plus (-y) < a := by
    have h := hj (-plus (-y)) (by simp [junctions])
    simp only [Set.mem_Icc, not_and] at h
    by_contra hn
    exact h (le_of_not_gt hn) (le_of_not_ge h1)
  by_cases h2 : b ≤ -minus (-y)
  · exact negative_cell hy hab h1'.le h2
  have h2' : -minus (-y) < a := by
    have h := hj (-minus (-y)) (by simp [junctions])
    simp only [Set.mem_Icc, not_and] at h
    by_contra hn
    exact h (le_of_not_gt hn) (le_of_not_ge h2)
  by_cases h3 : b ≤ minus y
  · apply hconstant 2
    intro x hx
    by_cases hp : 0 ≤ x
    · exact before hy hp (hx.2.trans h3)
    · rw [← neg_neg x, reflect]
      exact before (neg_parameter hy) (by linarith) (by linarith [hx.1])
  have h3' : minus y < a := by
    have h := hj (minus y) (by simp [junctions])
    simp only [Set.mem_Icc, not_and] at h
    by_contra hn
    exact h (le_of_not_gt hn) (le_of_not_ge h3)
  by_cases h4 : b ≤ plus y
  · exact positive_cell hy hab h3'.le h4
  have h4' : plus y < a := by
    have h := hj (plus y) (by simp [junctions])
    simp only [Set.mem_Icc, not_and] at h
    by_contra hn
    exact h (le_of_not_gt hn) (le_of_not_ge h4)
  apply hconstant 0
  intro x hx
  exact after hy (h4'.le.trans hx.1)

theorem junction_cell {y a b : ℝ} (hy : y ∈ Set.Icc (-1) 1) (hab : a ≤ b) :
    |error (fun x => F x y) a b| ≤ 18 * (b - a) ^ 2 :=
  TrapezoidalEstimate.lipschitz_cell hab (continuous y hy).continuousOn
    (fun x _ z _ => SliceUniformBounds.lipschitz hy x z)

end Cubic.AllGaloisCounts.SliceCellEstimate
