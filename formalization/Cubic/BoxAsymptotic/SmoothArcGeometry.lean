import CubicTargets.BoxAsymptotic.Statement
import Mathlib.Analysis.Normed.Group.AddCircle

/-! The angular support condition in `lem:smooth` is closed: although the
chosen representative `wrap` jumps at an endpoint, its absolute value is the
continuous distance on the circle. -/

noncomputable section

namespace Cubic.BoxAsymptotic.SmoothArcGeometry

open Set
open CubicTargets.BoxAsymptotic

theorem wrap_coe (x : ℝ) :
    (wrap x : AddCircle (2 * Real.pi)) = (x : AddCircle (2 * Real.pi)) := by
  change ((x - toIocDiv Real.two_pi_pos (-Real.pi) x • (2 * Real.pi) : ℝ) :
    AddCircle (2 * Real.pi)) = (x : AddCircle (2 * Real.pi))
  generalize toIocDiv Real.two_pi_pos (-Real.pi) x = n
  rw [AddCircle.coe_sub (2 * Real.pi), AddCircle.coe_zsmul (2 * Real.pi),
    AddCircle.coe_period (2 * Real.pi), smul_zero, sub_zero]

theorem abs_wrap_eq_norm (x : ℝ) :
    |wrap x| = ‖(x : AddCircle (2 * Real.pi))‖ := by
  have hw := toIocMod_mem_Ioc Real.two_pi_pos (-Real.pi) x
  have hnorm := (AddCircle.norm_coe_eq_abs_iff (2 * Real.pi) Real.two_pi_pos.ne'
    (x := wrap x)).mpr (show |wrap x| ≤ |2 * Real.pi| / 2 by
      rw [abs_of_pos Real.two_pi_pos]
      rw [abs_le]
      change -Real.pi < wrap x ∧ wrap x ≤ -Real.pi + 2 * Real.pi at hw
      constructor <;> linarith [hw.1, hw.2])
  rw [wrap_coe] at hnorm
  exact hnorm.symm

theorem continuous_abs_wrap : Continuous (fun x : ℝ => |wrap x|) := by
  simp_rw [abs_wrap_eq_norm]
  exact (continuous_quot_mk : Continuous (fun x : ℝ => (x : AddCircle (2 * Real.pi)))).norm

theorem support_region_closed (a b θ₀ Θ : ℝ) :
    IsClosed {p : ℝ × ℝ | a ≤ p.1 ∧ p.1 ≤ b ∧ |wrap (p.2 - θ₀)| ≤ 4 * Θ} := by
  have hrad : IsClosed {p : ℝ × ℝ | a ≤ p.1 ∧ p.1 ≤ b} :=
    isClosed_Icc.preimage continuous_fst
  have hang : IsClosed {p : ℝ × ℝ | |wrap (p.2 - θ₀)| ≤ 4 * Θ} :=
    isClosed_le (continuous_abs_wrap.comp (continuous_snd.sub continuous_const)) continuous_const
  convert hrad.inter hang using 1
  ext p
  simp only [mem_setOf_eq, mem_inter_iff, and_assoc]

end Cubic.BoxAsymptotic.SmoothArcGeometry
