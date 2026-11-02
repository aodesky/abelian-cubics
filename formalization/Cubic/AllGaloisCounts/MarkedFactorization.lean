import Cubic.AllGaloisCounts.HeightBox

/-! The root bound and the unique marked linear-factor parametrization from
the appendix. The parameters record actual polynomial coefficients. -/

noncomputable section

namespace Cubic.AllGaloisCounts.MarkedFactorization
open Polynomial CountData HeightBox Cubic.Counting.GeneralMonicData
open Cubic.Counting.GeneralHeightReduction

theorem cubic_root_bound {H t : ℝ} (hH : 0 ≤ H)
    (he : t ^ 3 ≤ H * t ^ 2 + H ^ 2 * t + H ^ 3) : t ≤ 2 * H := by
  by_contra hn
  have hlt : 2 * H < t := lt_of_not_ge hn
  have htp : 0 < t := lt_of_le_of_lt (by positivity) hlt
  have hq : 0 < t ^ 2 + H * t + H ^ 2 := by positivity
  have hp := mul_pos (sub_pos.mpr hlt) hq
  nlinarith [pow_nonneg hH 3]

/-- Every complex root is in the disk of radius `2H`, also for repeated roots. -/
theorem root_norm_bound {a b c : ℤ} {H : ℝ} {z : ℂ}
    (hh : weightedHeight (monicCubic a b c) ≤ H)
    (hr : ((monicCubic a b c).map (Int.castRingHom ℂ)).eval z = 0) :
    ‖z‖ ≤ 2 * H := by
  have hH : 0 ≤ H := (height_nonneg _).trans hh
  have hc := (HeightBox.height_iff hH).mp hh
  simp only [monicCubic_coeff_two, monicCubic_coeff_one, monicCubic_coeff_zero] at hc
  have he : z ^ 3 = -((a : ℂ) * z ^ 2 + (b : ℂ) * z + c) := by
    simp only [monicCubic, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_C, eval_add, eval_mul, eval_pow, eval_X,
      eval_C, Int.coe_castRingHom] at hr
    linear_combination hr
  apply cubic_root_bound hH
  calc ‖z‖ ^ 3 = ‖z ^ 3‖ := (norm_pow _ _).symm
    _ = ‖(a : ℂ) * z ^ 2 + (b : ℂ) * z + c‖ := by rw [he, norm_neg]
    _ ≤ ‖(a : ℂ) * z ^ 2‖ + ‖(b : ℂ) * z‖ + ‖(c : ℂ)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = |(a : ℝ)| * ‖z‖ ^ 2 + |(b : ℝ)| * ‖z‖ + |(c : ℝ)| := by
      simp only [norm_mul, norm_pow, Complex.norm_intCast]
    _ ≤ H * ‖z‖ ^ 2 + H ^ 2 * ‖z‖ + H ^ 3 := by
      gcongr
      · exact hc.1
      · exact hc.2.1
      · exact hc.2.2

theorem integral_root_bound {H : ℝ} {f : ℤ[X]} (hf : f ∈ cubicBox H)
    {r : ℤ} (hr : f.eval r = 0) : |(r : ℝ)| ≤ 2 * H := by
  obtain ⟨⟨a, b, c, rfl⟩, hh⟩ := hf
  have he : ((monicCubic a b c).map (Int.castRingHom ℂ)).eval (r : ℂ) = 0 := by
    simp only [monicCubic, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_C, eval_add, eval_mul, eval_pow, eval_X,
      eval_C, Int.coe_castRingHom] at hr ⊢
    exact_mod_cast hr
  simpa only [Complex.norm_intCast] using root_norm_bound hh he

theorem markedSet_finite (H : ℝ) : (markedSet H).Finite := by
  refine ((cubicBox_finite H).prod (Set.finite_Icc (-⌊2 * H⌋) ⌊2 * H⌋)).subset ?_
  rintro ⟨f, r⟩ ⟨hf, hr⟩
  exact ⟨hf, (int_abs_iff r (2 * H)).mp (integral_root_bound hf hr)⟩

def markedPolynomial (a r v : ℤ) : ℤ[X] :=
  monicCubic a (v - r * (r + a)) (-r * v)

theorem factorization (a r v : ℤ) :
    markedPolynomial a r v = (X - C r) * (X ^ 2 + C (a + r) * X + C v) := by
  simp only [markedPolynomial, monicCubic, map_sub, map_mul, map_add, map_neg]
  ring

theorem marked_root (a r v : ℤ) : (markedPolynomial a r v).eval r = 0 := by
  simp [factorization]

/-- The parameters in the manuscript are unique for a specified integral root. -/
theorem unique_parameters {f : ℤ[X]} (hf : ∃ a b c : ℤ, f = monicCubic a b c)
    {r : ℤ} (hr : f.eval r = 0) : ∃! av : ℤ × ℤ, f = markedPolynomial av.1 r av.2 := by
  obtain ⟨a, b, c, rfl⟩ := hf
  have hc : c = -r * (b + r * (r + a)) := by
    simp only [monicCubic, eval_add, eval_mul, eval_pow, eval_X, eval_C] at hr
    nlinarith
  refine ⟨(a, b + r * (r + a)), ?_, ?_⟩
  · simp only [markedPolynomial, add_sub_cancel_right, hc]
  · rintro ⟨a', v'⟩ he
    have ha := congrArg (fun p : ℤ[X] => p.coeff 2) he
    have hv := congrArg (fun p : ℤ[X] => p.coeff 1) he
    simp only [markedPolynomial, monicCubic_coeff_two, monicCubic_coeff_one] at ha hv
    exact Prod.ext ha.symm (by simp only [ha] at hv ⊢; linarith)

theorem marked_height_iff (a r v : ℤ) {H : ℝ} (hH : 0 ≤ H) :
    weightedHeight (markedPolynomial a r v) ≤ H ↔ |(a : ℝ)| ≤ H ∧
      |(v : ℝ) - r * (r + a)| ≤ H ^ 2 ∧ |(r : ℝ) * v| ≤ H ^ 3 := by
  rw [HeightBox.height_iff hH]
  simp only [markedPolynomial, monicCubic_coeff_two, monicCubic_coeff_one,
    monicCubic_coeff_zero, Int.cast_sub, Int.cast_mul, Int.cast_add, Int.cast_neg,
    neg_mul, abs_neg]

end Cubic.AllGaloisCounts.MarkedFactorization
