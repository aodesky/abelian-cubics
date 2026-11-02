import Cubic.BoxAsymptotic.HeckeOmitThree
import Cubic.BoxAsymptotic.AngularEulerProduct
import Cubic.BoxAsymptotic.AngularFactorBounds
import Cubic.BoxAsymptotic.AngularSeries

/-! Construction of the analytic functions in the moment target from genuine
Dirichlet series and the proved Euler identities. No moment estimate enters
this construction. Odd angular modes are zero by the original Fourier series.
-/

noncomputable section

namespace Cubic.BoxAsymptotic.HeckeAnalyticRealization

open Cubic.BoxAsymptotic.HeckePrimitiveCharacters
open Cubic.BoxAsymptotic.AngularMomentData Cubic.BoxAsymptotic.AngularIdealData
open Cubic.BoxAsymptotic.AngularLocalSeries
open Cubic.BoxAsymptotic.AngularFactorBounds

variable (hHecke : CubicTargets.BoxAsymptotic.PrimitiveHecke.BlackBox)

def primitiveL (k : ℤ) : ℂ → ℂ :=
  if h : Even k ∧ k ≠ 0 then (exists_analytic hHecke h.1 h.2).choose else 0

theorem primitive_entire {k : ℤ} (hk : Even k) (hk0 : k ≠ 0) :
    Differentiable ℂ (primitiveL hHecke k) := by
  rw [primitiveL, dif_pos ⟨hk, hk0⟩]
  exact (exists_analytic hHecke hk hk0).choose_spec.choose_spec.choose_spec.entire

theorem primitive_series {k : ℤ} (hk : Even k) (hk0 : k ≠ 0) (s : ℂ) (hs : 1 < s.re) :
    primitiveL hHecke k s = LSeries (HeckeSeriesConvergence.coefficient (primitiveHom k)) s := by
  rw [primitiveL, dif_pos ⟨hk, hk0⟩]
  exact (exists_analytic hHecke hk hk0).choose_spec.choose_spec.choose_spec.series_eq s hs

def heckeL (k : ℤ) (s : ℂ) : ℂ := HeckeOmitThree.factor k s * primitiveL hHecke k s

theorem hecke_entire {k : ℤ} (hk : Even k) (hk0 : k ≠ 0) :
    Differentiable ℂ (heckeL hHecke k) :=
  (HeckeOmitThree.factor_entire k).mul (primitive_entire hHecke hk hk0)

theorem hecke_series {k : ℤ} (hk : Even k) (hk0 : k ≠ 0) (s : ℂ) (hs : 1 < s.re) :
    heckeL hHecke k s = heckeSeries k s := by
  rw [heckeL, primitive_series hHecke hk hk0 s hs, HeckeOmitThree.series_eq k s hs]

theorem localFactor_holomorphic (k : ℤ) :
    DifferentiableOn ℂ (localFactor k) {s : ℂ | (1 / 2 : ℝ) < s.re} := by
  have hy : Differentiable ℂ (y k) :=
    (differentiable_const _).mul
      (differentiable_id.neg.const_cpow (.inl (by norm_num : (3 : ℂ) ≠ 0)))
  have hd : ∀ s ∈ {s : ℂ | (1 / 2 : ℝ) < s.re}, 1 - y k s ≠ 0 := by
    intro s hs he
    have hn := norm_y_le k s hs.le
    have hv := (sub_eq_zero.mp he).symm
    rw [hv, norm_one] at hn
    norm_num at hn
  exact (differentiableOn_const _).mul
    (((differentiableOn_const _).add hy.differentiableOn).add
      (((differentiableOn_const _).mul (hy.differentiableOn.pow 2)).div
        ((differentiableOn_const _).sub hy.differentiableOn) hd))

def angularF (k : ℤ) (s : ℂ) : ℂ :=
  if Even k then localFactor k s *
    (heckeL hHecke k s * heckeL hHecke (3 * k) s * AngularCorrectionProduct.value k s)
  else 0

theorem angular_holomorphic {k : ℤ} (hk0 : k ≠ 0) :
    DifferentiableOn ℂ (angularF hHecke k) {s : ℂ | (1 / 2 : ℝ) < s.re} := by
  by_cases hk : Even k
  · have h3k : 3 * k ≠ 0 := mul_ne_zero (by norm_num) hk0
    apply DifferentiableOn.congr ((localFactor_holomorphic k).mul
      (((hecke_entire hHecke hk hk0).differentiableOn.mul
        (hecke_entire hHecke (hk.mul_left 3) h3k).differentiableOn).mul
        (AngularCorrectionProduct.differentiableOn_value k)))
    intro s _
    exact if_pos hk
  · apply DifferentiableOn.congr (differentiableOn_const (0 : ℂ))
    intro s _
    exact if_neg hk

theorem angular_series
    {k : ℤ} (hk0 : k ≠ 0) (s : ℂ) (hs : 1 < s.re) :
    angularF hHecke k s = AngularSeriesData.series k s := by
  obtain ⟨_, hodd, heven⟩ := AngularSeries.«eq:Fk»
  by_cases hk : Even k
  · have hF : AngularSeriesData.series k s = localFactor k s * idealSeries k s := by
      simpa only [localFactor, y, AngularRamified.ramifiedPhase_even hk] using (heven k hk s hs).2
    rw [angularF, if_pos hk, hF, AngularEulerProduct.«eq:Dk» k hk s hs,
      hecke_series hHecke hk hk0 s hs,
      hecke_series hHecke (hk.mul_left 3) (mul_ne_zero (by norm_num) hk0) s hs]
  · rw [angularF, if_neg hk, hodd k (Int.not_even_iff_odd.mp hk) s]

theorem realization
    :
    AnalyticRealization (heckeL hHecke) (angularF hHecke) where
  hecke_entire _ := hecke_entire hHecke
  hecke_eq _ := hecke_series hHecke
  angular_holomorphic _ := angular_holomorphic hHecke
  angular_eq _ := angular_series hHecke

end Cubic.BoxAsymptotic.HeckeAnalyticRealization
