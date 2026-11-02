import Cubic.BoxAsymptotic.SmoothPartition
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Integrals of the partition profiles

`∫_0^∞ φ(u) du/u = log 2` (from `χ = 1` on `(0, 1]`, `χ = 0` on `[2, ∞)` and the
substitution `u ↦ 2u`), hence `∫ Φ = log 2` and `∫ Ψ = 2 log 2`. The angular integral of
the `2π`-periodic weight is `∫_0^{2π} Ψ(wrap(θ - θ₀)/Θ) dθ = 2Θ log 2` for `0 < Θ ≤ 1/4`.
-/

noncomputable section

namespace Cubic.BoxAsymptotic.PartitionIntegrals

open Real MeasureTheory Set Cubic.BoxAsymptotic.SmoothPartition
open CubicTargets.BoxAsymptotic (wrap)

/-- `g(w) = χ(w)/w`. -/
def g (w : ℝ) : ℝ := χ w / w

theorem g_cont {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : IntervalIntegrable g volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div χ_contDiff.continuous.continuousOn continuousOn_id
  intro x hx
  rw [uIcc_of_le hab] at hx
  exact (by linarith [hx.1] : (0 : ℝ) < x).ne'

theorem integral_Φ_interval : ∫ u in (1 / 4 : ℝ)..4, Φ u = Real.log 2 := by
  have e : ∀ u, Φ u = g u - 2 * g (2 * u) := fun u => by
    simp only [Φ, φ, g]
    rcases eq_or_ne u 0 with rfl | hu
    · simp
    · field_simp
  simp_rw [e]
  have hi2 : IntervalIntegrable (fun u => 2 * g (2 * u)) volume (1 / 4) 4 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.div (χ_contDiff.continuous.comp (continuous_const.mul continuous_id)).continuousOn
      (continuous_const.mul continuous_id).continuousOn
    intro x hx
    rw [uIcc_of_le (by norm_num)] at hx
    show 2 * x ≠ 0; linarith [hx.1]
  rw [intervalIntegral.integral_sub (g_cont (by norm_num) (by norm_num)) hi2]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_left _
    (by norm_num : (2 : ℝ) ≠ 0)]
  norm_num
  -- `∫_{1/4}^4 g - ∫_{1/2}^8 g = ∫_{1/4}^{1/2} g - ∫_4^8 g`
  rw [← intervalIntegral.integral_add_adjacent_intervals (g_cont (by norm_num) (by norm_num) :
      IntervalIntegrable g volume (1 / 4) (1 / 2)) (g_cont (by norm_num) (by norm_num) :
      IntervalIntegrable g volume (1 / 2) 4),
    ← intervalIntegral.integral_add_adjacent_intervals (g_cont (by norm_num) (by norm_num) :
      IntervalIntegrable g volume (1 / 2) 4) (g_cont (by norm_num) (by norm_num) :
      IntervalIntegrable g volume 4 8)]
  have h1 : ∫ w in (1 / 4 : ℝ)..(1 / 2), g w = Real.log 2 := by
    rw [intervalIntegral.integral_congr (g := fun w => 1 / w) fun w hw => by
      rw [uIcc_of_le (by norm_num)] at hw
      simp only [g, χ_eq_one (by linarith [hw.2] : w ≤ 1)]]
    rw [integral_one_div (by rw [uIcc_of_le (by norm_num)]; intro h; linarith [h.1])]
    norm_num
  have h2 : ∫ w in (4 : ℝ)..8, g w = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun w hw => by
      rw [uIcc_of_le (by norm_num)] at hw
      simp only [g, χ_eq_zero (by linarith [hw.1] : 2 ≤ w), zero_div]]
    simp
  rw [h1, h2]; ring


theorem Φ_eq_zero_of_not {u : ℝ} (h : u ∉ Ioc (1 / 4 : ℝ) 4) : Φ u = 0 := by
  by_contra hne
  have := Φ_support hne
  exact h ⟨by linarith [this.1], this.2⟩

theorem integral_Φ : ∫ u, Φ u = Real.log 2 := by
  rw [← intervalIntegral.integral_eq_integral_of_support_subset
    (fun u hu => by by_contra h; exact hu (Φ_eq_zero_of_not h)), integral_Φ_interval]

theorem integral_Φ_Ioi : ∫ u in Ioi (0 : ℝ), Φ u = Real.log 2 := by
  have h : ∀ u, u ∉ Ioi (0 : ℝ) → Φ u = 0 := fun u hu =>
    Φ_eq_zero_of_not fun h' => hu (show (0 : ℝ) < u by linarith [h'.1])
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero h, integral_Φ]

theorem Ψ_eq (v : ℝ) : Ψ v = Φ |v| := rfl

theorem integral_Ψ_interval : ∫ v in (-4 : ℝ)..4, Ψ v = 2 * Real.log 2 := by
  have hc : Continuous Ψ := Ψ_contDiff.continuous
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable (-4) 0)
    (hc.intervalIntegrable 0 4)]
  have h1 : ∫ v in (0 : ℝ)..4, Ψ v = ∫ v in (0 : ℝ)..4, Φ v :=
    intervalIntegral.integral_congr fun v hv => by
      rw [uIcc_of_le (by norm_num)] at hv
      rw [Ψ_eq, abs_of_nonneg hv.1]
  have h2 : ∫ v in (-4 : ℝ)..0, Ψ v = ∫ v in (0 : ℝ)..4, Φ v := by
    rw [show (∫ v in (-4 : ℝ)..0, Ψ v) = ∫ v in (-4 : ℝ)..0, Φ (-v) from
      intervalIntegral.integral_congr fun v hv => by
        rw [uIcc_of_le (by norm_num)] at hv
        rw [Ψ_eq, abs_of_nonpos hv.2],
      intervalIntegral.integral_comp_neg]
    norm_num
  have h3 : ∫ v in (0 : ℝ)..4, Φ v = Real.log 2 := by
    rw [← integral_Φ_interval, ← intervalIntegral.integral_add_adjacent_intervals
      (Φ_contDiff.continuous.intervalIntegrable 0 (1 / 4))
      (Φ_contDiff.continuous.intervalIntegrable (1 / 4) 4)]
    have : ∫ v in (0 : ℝ)..(1 / 4), Φ v = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun v hv => by
        rw [uIcc_of_le (by norm_num)] at hv
        exact Φ_eq_zero_of_not fun h => by linarith [h.1, hv.2]]
      simp
    rw [this, zero_add]
  rw [h1, h2, h3]; ring

theorem Ψ_support' : Function.support Ψ ⊆ Icc (-2) 2 := by
  intro v hv
  have : φ |v| ≠ 0 := by
    intro h; apply hv; rw [Ψ, h, zero_div]
  exact abs_le.mp (φ_support this).2

theorem integral_Ψ : ∫ v, Ψ v = 2 * Real.log 2 := by
  rw [← intervalIntegral.integral_eq_integral_of_support_subset
    (a := -4) (b := 4) (fun v hv => ⟨by linarith [(Ψ_support' hv).1], by linarith [(Ψ_support' hv).2]⟩),
    integral_Ψ_interval]

theorem integral_Ψ_scaled {Θ : ℝ} (hΘ : 0 < Θ) (hΘ' : Θ ≤ 1 / 4) :
    ∫ t in (-Real.pi)..Real.pi, Ψ (t / Θ) = Θ * (2 * Real.log 2) := by
  rw [intervalIntegral.integral_comp_div _ hΘ.ne']
  have hpi := Real.pi_gt_three
  have hb : 4 ≤ Real.pi / Θ := by rw [le_div_iff₀ hΘ]; nlinarith
  rw [intervalIntegral.integral_eq_integral_of_support_subset
    (fun v hv => ⟨by rw [neg_div]; linarith [(Ψ_support' hv).1], by linarith [(Ψ_support' hv).2]⟩),
    integral_Ψ, smul_eq_mul]


theorem wrap_add_two_pi (x : ℝ) : wrap (x + 2 * Real.pi) = wrap x := by
  simp only [wrap]; exact toIocMod_add_right _ _ _

theorem wrap_eq_self {x : ℝ} (h : x ∈ Ioc (-Real.pi) Real.pi) : wrap x = x := by
  simp only [wrap]
  rw [toIocMod_eq_self]
  exact ⟨h.1, by linarith [h.2]⟩

/-- **The angular integral**: `∫_0^{2π} Ψ(wrap(θ - θ₀)/Θ) dθ = 2Θ log 2`. -/
theorem integral_angle {Θ θ₀ : ℝ} (hΘ : 0 < Θ) (hΘ' : Θ ≤ 1 / 4) :
    ∫ θ in (0 : ℝ)..2 * Real.pi, Ψ (wrap (θ - θ₀) / Θ) = Θ * (2 * Real.log 2) := by
  have hper : Function.Periodic (fun θ => Ψ (wrap (θ - θ₀) / Θ)) (2 * Real.pi) := fun θ => by
    simp only; rw [show θ + 2 * Real.pi - θ₀ = θ - θ₀ + 2 * Real.pi by ring, wrap_add_two_pi]
  have h1 := hper.intervalIntegral_add_eq 0 (θ₀ - Real.pi)
  rw [zero_add] at h1
  rw [h1, show θ₀ - Real.pi + 2 * Real.pi = θ₀ + Real.pi by ring]
  have h2 : ∫ θ in (θ₀ - Real.pi)..(θ₀ + Real.pi), Ψ (wrap (θ - θ₀) / Θ) =
      ∫ θ in (θ₀ - Real.pi)..(θ₀ + Real.pi), Ψ ((θ - θ₀) / Θ) := by
    apply intervalIntegral.integral_congr_ae
    refine Filter.Eventually.of_forall fun θ hθ => ?_
    rw [uIoc_of_le (by linarith [Real.pi_pos])] at hθ
    rw [wrap_eq_self ⟨by linarith [hθ.1], by linarith [hθ.2]⟩]
  rw [h2, intervalIntegral.integral_comp_sub_right (fun t => Ψ (t / Θ)),
    show θ₀ - Real.pi - θ₀ = -Real.pi by ring, show θ₀ + Real.pi - θ₀ = Real.pi by ring,
    integral_Ψ_scaled hΘ hΘ']


open CubicTargets.BoxAsymptotic (weight aStar)

/-- `c₁ = ∫_0^∞ Φ(u) log u du`. -/
def c₁ : ℝ := ∫ u in Ioi (0 : ℝ), Φ u * Real.log u

theorem Φ_integrable : Integrable Φ :=
  Φ_contDiff.continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.intro isCompact_Icc fun u hu => by
      by_contra h; exact hu (Φ_support h))

theorem Φlog_integrable : Integrable fun u => Φ u * Real.log u := by
  have hcont : Continuous fun u => Φ u * Real.log u := by
    rw [continuous_iff_continuousAt]
    intro x
    rcases lt_or_ge x (1 / 4) with hx | hx
    · have : (fun u => Φ u * Real.log u) =ᶠ[nhds x] fun _ => 0 := by
        filter_upwards [Iio_mem_nhds (by linarith : x < 1 / 2)] with y hy
        rw [Φ, φ_eq_zero_of_le hy.le, zero_div, zero_mul]
      exact continuousAt_const.congr this.symm
    · exact Φ_contDiff.continuous.continuousAt.mul (Real.continuousAt_log (by linarith))
  exact hcont.integrable_of_hasCompactSupport
    (HasCompactSupport.intro isCompact_Icc fun u hu => by
      by_contra h
      apply hu
      have : Φ u ≠ 0 := fun h0 => h (by rw [h0, zero_mul])
      exact Φ_support this)

/-- **The main term of one piece**:
`∫_0^∞ ∫_0^{2π} w (a log n + b₀) dθ/(2π) dn = (Θ log 2/π) X ((a log X + b₀) log 2 + a c₁)`. -/
theorem main_integral {X Θ θ₀ b₀ : ℝ} (hX : 0 < X) (hΘ : 0 < Θ) (hΘ' : Θ ≤ 1 / 4) :
    ∫ n in Ioi (0 : ℝ), ∫ θ in (0 : ℝ)..2 * Real.pi,
        weight Φ Ψ X Θ θ₀ n θ * (aStar * Real.log n + b₀) / (2 * Real.pi) =
      Θ * Real.log 2 / Real.pi * X * ((aStar * Real.log X + b₀) * Real.log 2 + aStar * c₁) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hin : ∀ n : ℝ, ∫ θ in (0 : ℝ)..2 * Real.pi,
      weight Φ Ψ X Θ θ₀ n θ * (aStar * Real.log n + b₀) / (2 * Real.pi) =
      Θ * Real.log 2 / Real.pi * (Φ (n / X) * (aStar * Real.log n + b₀)) := fun n => by
    simp only [weight]
    have e : ∀ θ, Φ (n / X) * Ψ (wrap (θ - θ₀) / Θ) * (aStar * Real.log n + b₀) /
        (2 * Real.pi) = (Φ (n / X) * (aStar * Real.log n + b₀) / (2 * Real.pi)) *
          Ψ (wrap (θ - θ₀) / Θ) := fun θ => by ring
    simp_rw [e]
    rw [intervalIntegral.integral_const_mul, integral_angle hΘ hΘ']
    field_simp
  simp_rw [hin]
  rw [integral_const_mul]
  -- substitute `n = X u` `∫ G(n/X) dn = X ∫ G`
  have key : ∫ n in Ioi (0 : ℝ), Φ (n / X) * (aStar * Real.log n + b₀) =
      X * ∫ u in Ioi (0 : ℝ), Φ u * (aStar * Real.log (X * u) + b₀) := by
    have h := integral_comp_mul_left_Ioi (fun u => Φ u * (aStar * Real.log (X * u) + b₀))
      0 (inv_pos.mpr hX)
    simp only [mul_zero, inv_inv, smul_eq_mul] at h
    rw [← h]
    refine setIntegral_congr_fun measurableSet_Ioi fun n _ => ?_
    rw [div_eq_inv_mul, ← mul_assoc, mul_inv_cancel₀ hX.ne', one_mul]
  rw [key]
  have e3 : ∫ u in Ioi (0 : ℝ), Φ u * (aStar * Real.log (X * u) + b₀) =
      ∫ u in Ioi (0 : ℝ), ((aStar * Real.log X + b₀) * Φ u + aStar * (Φ u * Real.log u)) :=
    setIntegral_congr_fun measurableSet_Ioi fun u hu => by
      rw [Real.log_mul hX.ne' (ne_of_gt hu)]; ring
  rw [e3, integral_add (Φ_integrable.integrableOn.const_mul _)
    (Φlog_integrable.integrableOn.const_mul _), integral_const_mul, integral_const_mul,
    integral_Φ_Ioi, c₁]
  ring

end Cubic.BoxAsymptotic.PartitionIntegrals
