import Cubic.ToricHeights.AffineChartInvariants
import Cubic.ToricHeights.TernaryCyclicInvariants
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Data.Rat.Cast.CharZero

/-!
# Dehomogenization from `ℤ[X,Y,Z]` to the trace-one chart

`dehom` sends `X,Y,Z` to `x, y, z = 1-x-y`, i.e. `F ↦ F(X/ε, Y/ε, Z/ε)` for forms `F`
(on a form of degree `n` this is `F/εⁿ`). It intertwines the cyclic actions.
Every chart polynomial is the dehomogenization of a form (its homogenization), and
a form whose dehomogenization vanishes is zero: at a rational point with
`ε = X+Y+Z = t ≠ 0` a form of degree `n` takes the value `tⁿ` times its value at the
rescaled point on `ε = 1`, where it equals the dehomogenization; hence `F·ε` vanishes
at every rational point.
-/

noncomputable section

namespace Cubic.ToricHeights.ChartDehomogenization

open MvPolynomial AffineInvariantRing TernaryCyclicInvariants

/-- Dehomogenization `X ↦ x`, `Y ↦ y`, `Z ↦ 1-x-y`. -/
def dehom : TernaryRing →ₐ[ℤ] ChartRing := aeval ![X 0, X 1, thirdCoordinate]

@[simp] theorem dehom_X0 : dehom (X 0) = X 0 := by simp [dehom]
@[simp] theorem dehom_X1 : dehom (X 1) = X 1 := by simp [dehom]
@[simp] theorem dehom_X2 : dehom (X 2) = thirdCoordinate := by simp [dehom]

/-- `dehom` intertwines `rename (finRotate 3).symm` (`X ↦ Z`, `Y ↦ X`, `Z ↦ Y`) with the
chart generator `(x,y,z) ↦ (z,x,y)`. -/
theorem dehom_rename_symm (F : TernaryRing) :
    dehom (rename (finRotate 3).symm F) = cycle (dehom F) := by
  have h : dehom.comp (rename (finRotate 3).symm) = cycle.comp dehom := by
    apply MvPolynomial.algHom_ext
    intro i
    have h0 : (finRotate 3).symm 0 = 2 := by decide
    have h1 : (finRotate 3).symm 1 = 0 := by decide
    have h2 : (finRotate 3).symm 2 = 1 := by decide
    fin_cases i <;> simp [h0, h1, h2]
  exact congrArg (fun g : TernaryRing →ₐ[ℤ] ChartRing => g F) h

/-- `ε = X+Y+Z`. -/
def trace : TernaryRing := X 0 + X 1 + X 2

theorem trace_isHomogeneous : trace.IsHomogeneous 1 :=
  ((isHomogeneous_X ℤ 0).add (isHomogeneous_X ℤ 1)).add (isHomogeneous_X ℤ 2)

@[simp] theorem dehom_trace : dehom trace = 1 := by
  simp [trace, thirdCoordinate]

/-- Every chart polynomial is the dehomogenization of a form. -/
theorem exists_homogeneous_lift (f : ChartRing) :
    ∃ (n : ℕ) (F : TernaryRing), F.IsHomogeneous n ∧ dehom F = f := by
  set F0 : TernaryRing := rename (Fin.castSucc : Fin 2 → Fin 3) f
  have hF0 : dehom F0 = f := by
    have h : dehom.comp (rename (Fin.castSucc : Fin 2 → Fin 3)) = AlgHom.id ℤ ChartRing := by
      apply MvPolynomial.algHom_ext
      intro i
      fin_cases i <;> simp
    exact congrArg (fun g : ChartRing →ₐ[ℤ] ChartRing => g f) h
  refine ⟨F0.totalDegree, ∑ d ∈ Finset.range (F0.totalDegree + 1),
    homogeneousComponent d F0 * trace ^ (F0.totalDegree - d), ?_, ?_⟩
  · apply IsHomogeneous.sum
    intro d hd
    have hd' : d ≤ F0.totalDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)
    have h := (homogeneousComponent_isHomogeneous d F0).mul
      (trace_isHomogeneous.pow (F0.totalDegree - d))
    rwa [one_mul, Nat.add_sub_cancel' hd'] at h
  · simp only [map_sum, map_mul, map_pow, dehom_trace, one_pow, mul_one]
    rw [← map_sum, sum_homogeneousComponent, hF0]

/-- A form of degree `n` scales by `tⁿ`. -/
theorem eval_smul_of_isHomogeneous {σ : Type*} [Fintype σ] {R : Type*} [CommRing R]
    {φ : MvPolynomial σ R} {n : ℕ} (hφ : φ.IsHomogeneous n) (t : R) (x : σ → R) :
    eval (t • x) φ = t ^ n * eval x φ := by
  rw [eval_eq', eval_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdeg : ∑ i, d i = n := by
    have := hφ (mem_support_iff.mp hd)
    have h2 : d.degree = n := by rw [Finsupp.degree_eq_weight_one]; exact this
    rwa [Finsupp.degree_eq_sum] at h2
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hdeg]
  ring

/-- A form whose dehomogenization vanishes is zero. -/
theorem eq_zero_of_dehom_eq_zero {n : ℕ} {G : TernaryRing} (hG : G.IsHomogeneous n)
    (h : dehom G = 0) : G = 0 := by
  let c := Int.castRingHom ℚ
  have hc : Function.Injective c := Int.cast_injective
  -- evaluation of a form on the plane `ε = 1` factors through `dehom`
  have hplane : ∀ s : Fin 3 → ℚ, s 0 + s 1 + s 2 = 1 → eval s (map c G) = 0 := by
    intro s hs
    have hring : (eval s).comp (map c) =
        ((eval ![s 0, s 1]).comp (map c)).comp dehom.toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro a; simp [c]
      · intro i
        fin_cases i
        · simp [c]
        · simp [c]
        · simp [c, thirdCoordinate]; linear_combination hs
    have := congrArg (fun g : TernaryRing →+* ℚ => g G) hring
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h, map_zero] at this
    exact this
  have hGq : (map c G).IsHomogeneous n := hG.map c
  have hprod : map c (G * trace) = 0 := by
    apply MvPolynomial.funext
    intro r
    simp only [map_mul, map_zero]
    have htr : eval r (map c trace) = r 0 + r 1 + r 2 := by simp [trace, c]
    rw [htr]
    by_cases ht : r 0 + r 1 + r 2 = 0
    · rw [ht, mul_zero]
    · have hr : r = (r 0 + r 1 + r 2) • ((r 0 + r 1 + r 2)⁻¹ • r) := by
        rw [smul_smul, mul_inv_cancel₀ ht, one_smul]
      rw [hr, eval_smul_of_isHomogeneous hGq, hplane]
      · simp
      · simp only [Pi.smul_apply, smul_eq_mul]
        field_simp
  have htrace : trace ≠ 0 := by
    intro h0
    have := congrArg dehom h0
    simp at this
  have h0 : G * trace = 0 := map_injective c hc (by rw [hprod, map_zero])
  exact (mul_eq_zero.mp h0).resolve_right htrace

end Cubic.ToricHeights.ChartDehomogenization
