import Cubic.SantensComparison.LogDifferentials
import Cubic.SantensComparison.FanArithmetic
import Cubic.PoissonSummation.ArchimedeanFourier
import Mathlib.Algebra.MonoidAlgebra.Basic

/-! The actual affine toric chart of the ray v₀: its dual semigroup is
ℕ × ℤ in the monomial coordinates u=ν⁻¹, w=ν/ν̄. Quadratic descent on
this chart fixes the unit circle on u=0. The original height gives norm
one to the logarithmic form on a punctured neighborhood of that boundary. -/

noncomputable section

namespace Cubic.SantensComparison.RealBoundaryChart

open FanData Cubic.SurfaceGeometry.ResolutionData
open Cubic.ToricHeights Cubic.QuadraticCorrespondence

def rayCharacters : AddSubmonoid (ℤ × ℤ) where
  carrier := {m | 0 ≤ pairing m 0}
  zero_mem' := by simp [pairing]
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, pairing, Prod.fst_add, Prod.snd_add] at *
    nlinarith

def boundaryExponent : (ℕ × ℤ) →+ rayCharacters where
  toFun x := ⟨(x.2-x.1,-x.2), by simp [rayCharacters, pairing, rays]⟩
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp <;> ring

theorem boundary_exponent_bijective : Function.Bijective boundaryExponent := by
  constructor
  · rintro ⟨a,b⟩ ⟨c,d⟩ h
    have h₁ := congrArg (fun x : rayCharacters => x.val.1) h
    have h₂ := congrArg (fun x : rayCharacters => x.val.2) h
    dsimp [boundaryExponent] at h₁ h₂
    have hbd : b = d := by omega
    have hac : a = c := by omega
    simp [hbd, hac]
  · rintro ⟨⟨a,b⟩,h⟩
    have hab : 0 ≤ -a-b := by simpa [rayCharacters, pairing, rays] using h
    refine ⟨⟨(-a-b).toNat,-b⟩, ?_⟩
    ext <;> simp [boundaryExponent, Int.toNat_of_nonneg hab]
    omega

def boundaryCharacterEquiv : (ℕ × ℤ) ≃+ rayCharacters :=
  AddEquiv.ofBijective boundaryExponent boundary_exponent_bijective

/-- The coordinate algebra is the semigroup algebra of the actual dual ray. -/
def chartAlgebraEquiv (k : Type*) [CommRing k] :
    AddMonoidAlgebra k (ℕ × ℤ) ≃ₐ[k] AddMonoidAlgebra k rayCharacters :=
  AddMonoidAlgebra.domCongr k k boundaryCharacterEquiv

theorem coordinate_exponents :
    (boundaryExponent (1,0)).val = (-1,0) ∧
    (boundaryExponent (0,1)).val = (1,-1) := by decide

abbrev Chart := ℂ × ℂˣ

def torusToChart (s t : ℂˣ) : Chart := ((s : ℂ)⁻¹,s*t⁻¹)

def realDescent (x : Chart) : Chart :=
  (star x.1 * (star x.2 : ℂˣ), (star x.2)⁻¹)

theorem descent_involutive : Function.Involutive realDescent := by
  intro x
  ext <;> simp [realDescent]

theorem descent_on_torus (s t : ℂˣ) :
    realDescent (torusToChart s t) = torusToChart (star t) (star s) := by
  ext <;> simp [realDescent, torusToChart, mul_comm]

theorem fixed_boundary (w : ℂˣ) :
    realDescent (0,w) = (0,w) ↔ ‖(w:ℂ)‖=1 := by
  have h : (star w)⁻¹ = w ↔ star (w:ℂ) = (w:ℂ)⁻¹ := by
    rw [inv_eq_iff_eq_inv]
    simpa using (Units.ext_iff (u := star w) (v := w⁻¹))
  simpa only [realDescent, star_zero, zero_mul, Prod.mk.injEq, true_and, h]
    using LogDifferentials.boundary_real_locus w

def realBoundaryEquiv : {x : Chart // x.1=0 ∧ realDescent x=x} ≃ Circle where
  toFun x := ⟨(x.val.2:ℂ), by
    change (x.val.2:ℂ) ∈ Metric.sphere 0 1
    rw [mem_sphere_zero_iff_norm]
    apply (fixed_boundary x.val.2).mp
    have hx : (0,x.val.2)=x.val := Prod.ext x.property.1.symm rfl
    rw [hx]
    exact x.property.2⟩
  invFun w := ⟨(0,Units.mk0 (w:ℂ) w.coe_ne_zero), by
    refine ⟨rfl,(fixed_boundary _).mpr ?_⟩
    exact w.norm_coe⟩
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · exact x.property.1.symm
    · apply Units.ext
      rfl
  right_inv w := by apply Subtype.ext; rfl

def realBoundaryHomeomorph : {x : Chart // x.1=0 ∧ realDescent x=x} ≃ₜ Circle where
  toEquiv := realBoundaryEquiv
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact Units.continuous_val.comp (continuous_snd.comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_const.prodMk
    apply Units.continuous_iff.mpr
    constructor
    · exact continuous_subtype_val
    · change Continuous (fun w : Circle => (w:ℂ)⁻¹)
      exact continuous_subtype_val.inv₀ (fun w => Circle.coe_ne_zero w)

theorem real_boundary_nonempty :
    ∃ x : Chart, x.1=0 ∧ realDescent x=x :=
  ⟨(0,1),rfl,(fixed_boundary 1).mpr (by simp)⟩

/-- The height at the original complex place, in the original quotient-point
model, equals the radius whenever that radius is at least one. -/
theorem original_height_near_boundary (P : ArchimedeanQuotientLogarithm.Points)
    (hP : 1 ≤ ‖(CyclotomicArchimedean.pointEquiv P : ℂ)‖) :
    ArchimedeanQuotientLogarithm.inverseHeight (-1) 0 P =
      (‖(CyclotomicArchimedean.pointEquiv P : ℂ)‖ : ℂ) := by
  rw [ArchimedeanQuotientLogarithm.inverseHeight_eq]
  change Cubic.PoissonSummation.ArchimedeanFourier.inverseHeight (-1) 0
    (ArchimedeanQuotientLogarithm.coordinate P) = _
  rw [Cubic.PoissonSummation.ArchimedeanFourier.inverseHeight_nonneg (-1) 0
    (show 0 ≤ ArchimedeanQuotientLogarithm.coordinate P from Real.log_nonneg hP)]
  simp only [neg_neg, one_mul, ArchimedeanQuotientLogarithm.coordinate]
  rw [← Complex.ofReal_exp, Real.exp_log (by linarith)]

theorem metric_density_near_boundary (P : ArchimedeanQuotientLogarithm.Points)
    (hP : 1 ≤ ‖(CyclotomicArchimedean.pointEquiv P : ℂ)‖) :
    (ArchimedeanQuotientLogarithm.inverseHeight (-1) 0 P).re ^ (-2 : ℤ) *
      ‖(CyclotomicArchimedean.pointEquiv P : ℂ)‖^2 = 1 := by
  rw [original_height_near_boundary P hP, Complex.ofReal_re]
  have h : ‖(CyclotomicArchimedean.pointEquiv P : ℂ)‖ ≠ 0 := by linarith
  simp only [zpow_neg, zpow_ofNat]
  exact inv_mul_cancel₀ (pow_ne_zero 2 h)

end Cubic.SantensComparison.RealBoundaryChart
