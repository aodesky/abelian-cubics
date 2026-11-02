import CubicTargets.BoxAsymptotic.PrimitiveHecke

/-! Applicability of the primitive Hecke theorem to the actual even-frequency
ideal characters.  The finite quotient and the principal-ideal formula are
checked in both conductor cases, rather than being assumed with the theorem.
-/

noncomputable section

namespace Cubic.BoxAsymptotic.HeckePrimitiveCharacters

open Cubic.PoissonSummation.CyclotomicIntegerUnits
open Cubic.BoxAsymptotic.AngularIdealData Cubic.BoxAsymptotic.IdealAngularData
open Cubic.BoxAsymptotic.AngularSeriesData Cubic.BoxAsymptotic.HeckeGeneratorPhases
open Cubic.BoxAsymptotic.HeckeFiniteCharacter Cubic.BoxAsymptotic.HeckeConductor
open Cubic.BoxAsymptotic.PrimitiveHeckeData

theorem ramified_principal (k : ℤ) :
    PrincipalFormula reduction (finiteCharacter k) k (psiHom k) := by
  constructor
  · intro x hx u hu
    have h3 : ¬ 3 ∣ Ideal.absNorm (Ideal.span {x}) :=
      (HeckeModulus.reduction_isUnit_iff_norm x).mp (hu ▸ u.isUnit)
    let v : Integersˣ := residueUnitsEquiv.symm u
    have hv : reductionUnits v = u := residueUnitsEquiv.apply_symm_apply u
    have hr : reduction (v : Integers) = reduction x := by
      calc
        _ = (u : ResidueRing) := congrArg Units.val hv
        _ = _ := hu
    have h := principal_formula k hx h3 v hr
    simpa only [hv] using h
  · intro x _ hx
    have h3 : 3 ∣ Ideal.absNorm (Ideal.span {x}) := by
      by_contra h
      exact hx ((HeckeModulus.reduction_isUnit_iff_norm x).mpr h)
    change psi k (Ideal.span {x}) = 0
    rw [psi, if_pos h3]

theorem ramified_data {k : ℤ} (hk : ¬ 3 ∣ k) :
    ArithmeticData reduction (finiteCharacter k) k (psiHom k) where
  surjective := HeckeModulus.reduction_surjective
  kernel_nonzero := by rw [HeckeModulus.ker_reduction]; simp
  unitary := norm_finiteCharacter k
  primitive := finiteCharacter_primitive hk
  principal := ramified_principal k

def unramifiedHom {k : ℤ} (hk : 6 ∣ k) : Ideal Integers →*₀ ℂ where
  toFun := generatorPhase k
  map_zero' := by simp [generatorPhase]
  map_one' := generatorPhase_one hk
  map_mul' := generatorPhase_mul hk

def trivialReduction : Integers →+* ZMod 1 where
  toFun _ := 0
  map_zero' := rfl
  map_one' := Subsingleton.elim _ _
  map_add' _ _ := Subsingleton.elim _ _
  map_mul' _ _ := Subsingleton.elim _ _

theorem trivial_kernel : RingHom.ker trivialReduction = ⊤ := by
  ext x
  simp [RingHom.mem_ker, trivialReduction]

theorem unramified_principal {k : ℤ} (hk : 6 ∣ k) :
    PrincipalFormula trivialReduction (1 : (ZMod 1)ˣ →* ℂ) k (unramifiedHom hk) := by
  constructor
  · intro x hx u _
    simpa only [MonoidHom.one_apply, one_mul] using phase_span hk hx
  · intro x _ hx
    exact (hx (by rw [Subsingleton.elim (trivialReduction x) 1]; exact isUnit_one)).elim

theorem unramified_data {k : ℤ} (hk : 6 ∣ k) :
    ArithmeticData trivialReduction (1 : (ZMod 1)ˣ →* ℂ) k (unramifiedHom hk) where
  surjective := fun x => ⟨0, Subsingleton.elim _ _⟩
  kernel_nonzero := by rw [trivial_kernel]; exact top_ne_bot
  unitary := by intro u; simp
  primitive := by intro J _ _; exact Subsingleton.elim _ _
  principal := unramified_principal hk

theorem scale_one : scale (ZMod 1) = Real.sqrt 3 / (2 * Real.pi) := by
  simp [scale, Cubic.PoissonSummation.QuadraticDedekindResidue.discriminant]

theorem scale_nine : scale ResidueRing = Real.sqrt 27 / (2 * Real.pi) := by
  have hc : Fintype.card ResidueRing = 9 := by decide
  norm_num [scale, hc, Cubic.PoissonSummation.QuadraticDedekindResidue.discriminant]

def primitiveHom (k : ℤ) : Ideal Integers →*₀ ℂ :=
  if h : 6 ∣ k then unramifiedHom h else psiHom k

theorem primitiveHom_eq (k : ℤ) (I : Ideal Integers) : primitiveHom k I = primitivePsi k I := by
  unfold primitiveHom primitivePsi
  split_ifs <;> rfl

def conductorScale (k : ℤ) : ℝ :=
  if 6 ∣ k then Real.sqrt 3 / (2 * Real.pi) else Real.sqrt 27 / (2 * Real.pi)

/-- Existence of the primitive analytic L-functions, now with the arithmetic
hypotheses of the explicitly cited Hecke theorem discharged. This does not yet
remove the factor at three, or supply approximate-functional-equation weights. -/
theorem exists_analytic
    (hHecke : CubicTargets.BoxAsymptotic.PrimitiveHecke.BlackBox)
    {k : ℤ} (hk : Even k) (hk0 : k ≠ 0) :
    ∃ (L Λ : ℂ → ℂ) (ε : ℂ), AnalyticData (primitiveHom k) (conductorScale k) k L Λ ε := by
  by_cases h6 : 6 ∣ k
  · simpa only [primitiveHom, dif_pos h6, conductorScale, if_pos h6, scale_one] using
      hHecke (ZMod 1) trivialReduction 1 k (unramifiedHom h6) (unramified_data h6) hk0
  · have h3 : ¬ 3 ∣ k := by
      have h2 := even_iff_two_dvd.mp hk
      omega
    simpa only [primitiveHom, dif_neg h6, conductorScale, if_neg h6, scale_nine] using
      hHecke ResidueRing reduction (finiteCharacter k) k (psiHom k) (ramified_data h3) hk0

end Cubic.BoxAsymptotic.HeckePrimitiveCharacters
