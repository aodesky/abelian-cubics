import Cubic.PoissonSummation.FiniteAdelicData
import Cubic.ToricHeights.ArchimedeanQuotientLogarithm

/-!
# Adelic height and logarithmic character on the original quotient

Combine the original real point group with the finite restricted product.
The height is the product of the archimedean and finite residue-weighted
constructions, and the logarithm is the sum of their place contributions.
Its exponential character has the exact local components already calculated.

These are constructions on the adelic point group. Triviality on the rational
diagonal and descent to the automorphic quotient are proved separately in
`AdelicRationalCharacter` using the rational embedding and product formula;
they are not assumed here.
-/

noncomputable section

namespace Cubic.PoissonSummation.AdelicData

open Cubic.ToricHeights Cubic.QuadraticCorrespondence
open LocalLogarithmNormalization QuotientFiniteFourierProduct
open scoped RegularFunctionTopology RationalQuotientGroup QuotientLocalTopology

/-- Original real quotient points together with the original finite restricted product. -/
abbrev Points := ArchimedeanQuotientLogarithm.Points × FiniteAdelicData.Points

/-- The inverse adelic height, before imposing the finite invariant-integrality cutoff. -/
def inverseHeight (s₀ σ : ℂ) (x : Points) : ℂ :=
  ArchimedeanQuotientLogarithm.inverseHeight s₀ σ x.1 *
    FiniteAdelicData.inverseHeight s₀ σ x.2

/-- Sum of all splitting-field place contributions, with their original weights. -/
def logarithm (x : Points) : ℝ × ℝ :=
  ArchimedeanQuotientLogarithm.logarithm x.1 + FiniteAdelicData.logarithm x.2

theorem logarithm_mul (x y : Points) : logarithm (x * y) = logarithm x + logarithm y := by
  simp only [logarithm, Prod.fst_mul, Prod.snd_mul,
    ArchimedeanQuotientLogarithm.logarithm_mul, FiniteAdelicData.logarithm_mul]
  abel

@[simp]
theorem logarithm_one : logarithm 1 = 0 := by simp [logarithm]

theorem logarithm_invariant (x : Points) : (logarithm x).1 = (logarithm x).2 := by
  simp only [logarithm, Prod.fst_add, Prod.snd_add,
    ArchimedeanQuotientLogarithm.logarithm_eq, FiniteAdelicData.logarithm_invariant]

theorem continuous_logarithm : Continuous logarithm :=
  (ArchimedeanQuotientLogarithm.continuous_logarithm.comp continuous_fst).add
    (FiniteAdelicData.continuous_logarithm.comp continuous_snd)

theorem continuous_inverseHeight (s₀ σ : ℂ) : Continuous (inverseHeight s₀ σ) :=
  ((ArchimedeanQuotientLogarithm.continuous_inverseHeight s₀ σ).comp continuous_fst).mul
    ((FiniteAdelicData.continuous_inverseHeight s₀ σ).comp continuous_snd)

private theorem spectral_exp_add (t : ℝ) (u v : ℝ × ℝ) :
    Circle.exp (2 * Real.pi * spectralPairing t (u + v)) =
      Circle.exp (2 * Real.pi * spectralPairing t u) *
        Circle.exp (2 * Real.pi * spectralPairing t v) := by
  rw [← Circle.exp_add]
  congr 1
  dsimp [spectralPairing]
  ring

/-- The paper's exponential formula on the adelic point group.
Automorphic descent is proved separately in `AdelicRationalCharacter`. -/
def character (t : ℝ) : PontryaginDual Points where
  toFun x := Circle.exp (2 * Real.pi * spectralPairing t (logarithm x))
  map_one' := by simp [spectralPairing]
  map_mul' x y := by rw [logarithm_mul, spectral_exp_add]
  continuous_toFun := by
    have h : Continuous (fun n : ℝ × ℝ => 2 * Real.pi * spectralPairing t n) := by
      unfold spectralPairing
      fun_prop
    exact Circle.exp.continuous.comp (h.comp continuous_logarithm)

theorem character_apply (t : ℝ) (x : Points) :
    character t x = Circle.exp (2 * Real.pi * spectralPairing t (logarithm x)) := rfl

@[simp]
theorem character_zero : character 0 = 1 := by
  apply DFunLike.ext
  intro x
  change Circle.exp (2 * Real.pi * spectralPairing 0 (logarithm x)) = 1
  simp [spectralPairing]

theorem character_eq_components (t : ℝ) (x : Points) :
    character t x = ArchimedeanQuotientLogarithm.character t x.1 *
      FiniteAdelicData.character t x.2 := by
  rw [character_apply, logarithm, spectral_exp_add]
  rfl

/-- The character factors as its actual archimedean component times the convergent finite product. -/
theorem character_eq_product (t : ℝ) (x : Points) :
    character t x = ArchimedeanQuotientLogarithm.character t x.1 *
      ∏' p : Nat.Primes, (family p).character t (x.2 p) := by
  rw [character_eq_components, FiniteAdelicData.character_eq_tprod]

def includeFinite (p : Nat.Primes) (x : (family p).Carrier) : Points :=
  (1, FiniteAdelicData.includeLocal p x)

def includeInfinite (x : ArchimedeanQuotientLogarithm.Points) : Points := (x, 1)

theorem continuous_includeFinite (p : Nat.Primes) : Continuous (includeFinite p) :=
  continuous_const.prodMk (FiniteAdelicData.continuous_includeLocal p)

theorem continuous_includeInfinite : Continuous includeInfinite :=
  continuous_id.prodMk continuous_const

theorem inverseHeight_includeFinite (p : Nat.Primes) (s₀ σ : ℂ) (x : (family p).Carrier) :
    inverseHeight s₀ σ (includeFinite p x) = (family p).inverseHeight s₀ σ x := by
  simp [inverseHeight, includeFinite, FiniteAdelicData.inverseHeight_includeLocal]

theorem inverseHeight_includeInfinite (s₀ σ : ℂ) (x : ArchimedeanQuotientLogarithm.Points) :
    inverseHeight s₀ σ (includeInfinite x) = ArchimedeanQuotientLogarithm.inverseHeight s₀ σ x := by
  simp [inverseHeight, includeInfinite]

theorem logarithm_includeFinite (p : Nat.Primes) (x : (family p).Carrier) :
    logarithm (includeFinite p x) = FiniteAdelicData.localLogarithm p x := by
  simp [logarithm, includeFinite, FiniteAdelicData.logarithm_includeLocal]

theorem logarithm_includeInfinite (x : ArchimedeanQuotientLogarithm.Points) :
    logarithm (includeInfinite x) = ArchimedeanQuotientLogarithm.logarithm x := by
  simp [logarithm, includeInfinite]

theorem character_includeFinite (p : Nat.Primes) (t : ℝ) (x : (family p).Carrier) :
    character t (includeFinite p x) = (family p).character t x := by
  rw [character_eq_components]
  simp [includeFinite, FiniteAdelicData.character_includeLocal]

theorem character_includeInfinite (t : ℝ) (x : ArchimedeanQuotientLogarithm.Points) :
    character t (includeInfinite x) = ArchimedeanQuotientLogarithm.character t x := by
  rw [character_eq_components]
  simp [includeInfinite]

/-- The original positive real section with identity at every finite place. -/
def radialSection (u : ℝ) : Points := includeInfinite (ArchimedeanQuotientLogarithm.radialSection u)

theorem continuous_radialSection : Continuous radialSection :=
  continuous_includeInfinite.comp ArchimedeanQuotientLogarithm.continuous_radialSection

theorem logarithm_radialSection (u : ℝ) : logarithm (radialSection u) = (-u, -u) := by
  rw [radialSection, logarithm_includeInfinite, ArchimedeanQuotientLogarithm.logarithm_radialSection]

theorem inverseHeight_radialSection (s₀ σ : ℂ) (u : ℝ) :
    inverseHeight s₀ σ (radialSection u) = Complex.exp (supportFunction s₀ σ (-u, -u)) := by
  rw [radialSection, inverseHeight_includeInfinite,
    ArchimedeanQuotientLogarithm.inverseHeight_radialSection]

theorem character_radialSection (t u : ℝ) :
    character t (radialSection u) = Circle.exp (2 * Real.pi * t * u) := by
  rw [radialSection, character_includeInfinite, ArchimedeanQuotientLogarithm.character_radialSection]

end Cubic.PoissonSummation.AdelicData
