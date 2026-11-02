import Cubic.Introduction.EisensteinPointData
import Cubic.BoxAsymptotic.LocalTraceAtThree
import Cubic.ToricHeights.CanonicalHeight

/-! The integral-point/primary-element bijection is the map
`α ↦ N(α)α`. Integrality follows from the oriented invariant `δ`;
the inverse uses the primary trace congruence modulo 27. -/

noncomputable section

namespace Cubic.Introduction.IntegralEisenstein

open EisensteinPointData
open Cubic.QuadraticCorrespondence CyclotomicField CyclotomicTorusGalois
open DescendedCoefficients RationalCoefficientFormula
open Cubic.ToricHeights AffinePointComparison
open Cubic.PoissonSummation.CyclotomicIntegerUnits
open Cubic.BoxAsymptotic.PrimaryGenerator
open Cubic.Counting.EisensteinNormCount

theorem norm_resolvent (α : E) :
    Algebra.norm ℚ (resolvent α) = Algebra.norm ℚ α ^ 3 := by
  apply (algebraMap ℚ E).injective
  simp only [EisensteinPointData.resolvent, norm_eq_mul_conjugation, map_mul, map_pow,
    AlgEquiv.commutes]
  rw [conjugation_involutive]
  ring

theorem resolvent_injective : Function.Injective resolvent := by
  intro α β h
  have hn : Algebra.norm ℚ α = Algebra.norm ℚ β := by
    have h3 := congrArg (Algebra.norm ℚ) h
    rw [norm_resolvent, norm_resolvent] at h3
    exact (show Odd 3 by decide).pow_injective h3
  by_cases ha : α = 0
  · subst α
    have : β = 0 := by
      by_contra hβ
      have := norm_pos hβ
      simp only [Algebra.norm_zero] at hn
      linarith
    exact this.symm
  have hN : algebraMap ℚ E (Algebra.norm ℚ α) ≠ 0 :=
    (_root_.map_ne_zero _).mpr (norm_pos ha).ne'
  exact mul_left_cancel₀ hN (by simpa only [EisensteinPointData.resolvent, ← hn] using h)

theorem norm_parameter (P : TorusPoints) :
    Algebra.norm ℚ (parameterEquiv P : E) = 1 - 3 * P linearCoefficient := by
  rw [linearCoefficient_eq]
  ring

theorem resolvent_coordinates (P : TorusPoints) {a b d : ℤ}
    (ha : P linearCoefficient = a) (hb : P constantCoefficient = b)
    (hd : P DescendedCyclicInvariant.delta = d) :
    pointResolvent P =
      (coord (1 - 6 * a - 18 * b + 3 * d, 6 * d - 3 * a - 9 * b) : E) := by
  have h := AffinePointParameter.parameter_equation P
  rw [ha, hb, hd] at h
  simp only [pointResolvent, EisensteinPointData.resolvent, norm_parameter, ha, map_sub, map_one,
    map_mul, map_ofNat, map_intCast, coe_coord, sqrtNegThree] at h ⊢
  push_cast
  linear_combination h / 2

theorem integral_resolvent (P : IntegralTorus) :
    ∃ β : PrimaryCubes, (β.1 : E) = pointResolvent P.1 := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ :=
    (Cubic.PoissonSummation.IntegralPointComparison.coefficient_criterion P.1).mp P.2
  obtain ⟨d, hd⟩ := P.2
    ⟨AffineChartInvariants.delta, AffineChartInvariants.delta_mem⟩
  change P.1 (AffineInvariantRing.invariantRestriction _) = (d : ℚ) at hd
  rw [invariantRestriction_delta] at hd
  let p : ℤ × ℤ := (1 - 6 * a - 18 * b + 3 * d, 6 * d - 3 * a - 9 * b)
  have he : pointResolvent P.1 = (coord p : E) := resolvent_coordinates P.1 ha hb hd
  have hN : 0 ≤ 1 - 3 * a := by
    have hn := norm_pos (parameterEquiv P.1).ne_zero
    rw [norm_parameter, ha] at hn
    exact_mod_cast hn.le
  refine ⟨⟨coord p, ?_, ?_⟩, he.symm⟩
  · apply (isPrimary_coord p).mpr
    constructor
    · apply Int.modEq_iff_dvd.mpr
      exact ⟨2 * a + 6 * b - d, by dsimp [p]; ring⟩
    · exact ⟨2 * d - a - 3 * b, by dsimp [p]; ring⟩
  · refine ⟨(1 - 3 * a).toNat, ?_⟩
    rw [← he, pointResolvent, norm_resolvent, norm_parameter, ha]
    have hi : ((1 - 3 * a).toNat : ℤ) = 1 - 3 * a := Int.toNat_of_nonneg hN
    have hiq : ((1 - 3 * a).toNat : ℚ) = 1 - 3 * (a : ℚ) := by exact_mod_cast hi
    rw [hiq]

def toPrimary (P : IntegralTorus) : PrimaryCubes := (integral_resolvent P).choose

theorem toPrimary_val (P : IntegralTorus) :
    ((toPrimary P).1 : E) = pointResolvent P.1 := (integral_resolvent P).choose_spec

theorem toPrimary_injective : Function.Injective toPrimary := by
  intro P Q h
  apply Subtype.ext
  apply parameterEquiv.injective
  apply Units.ext
  apply resolvent_injective
  exact (toPrimary_val P).symm.trans
    ((congrArg (fun β : PrimaryCubes => (β.1 : E)) h).trans (toPrimary_val Q))

theorem norm_coord_rational (p : ℤ × ℤ) :
    Algebra.norm ℚ (coord p : E) =
      ((p.1 ^ 2 - p.1 * p.2 + p.2 ^ 2 : ℤ) : ℚ) := by
  have h := norm_linear (p.1 : ℚ) (p.2 : ℚ)
  simp only [coe_coord, map_intCast, CyclotomicCoefficients.normForm,
    Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_pow] at h ⊢
  linear_combination h

theorem trace_coord_rational (p : ℤ × ℤ) :
    Algebra.trace ℚ E (coord p : E) = ((2 * p.1 - p.2 : ℤ) : ℚ) := by
  have h := trace_linear (p.1 : ℚ) (p.2 : ℚ)
  simpa only [coe_coord, map_intCast, CyclotomicCoefficients.traceForm,
    Int.cast_sub, Int.cast_mul, Int.cast_ofNat] using h

theorem primary_ne_zero (β : PrimaryCubes) : (β.1 : E) ≠ 0 := by
  intro h
  have hz : β.1 = 0 := Subtype.ext h
  have hp := β.2.1
  simp [IsPrimary, hz] at hp

theorem toPrimary_surjective : Function.Surjective toPrimary := by
  intro β
  obtain ⟨M, hM⟩ := β.2.2
  have hpos : 0 < (M : ℚ) := by
    have h := norm_pos (primary_ne_zero β)
    rw [hM] at h
    by_contra hn
    have hzero : M = 0 := by exact_mod_cast (le_antisymm (le_of_not_gt hn) (Nat.cast_nonneg M))
    simp [hzero] at h
  have hM0 : (M : E) ≠ 0 := by exact_mod_cast hpos.ne'
  obtain ⟨p, hp⟩ := coord_surjective β.1
  have hprimary : p ∈ Cubic.BoxAsymptotic.AngularLocalData.primary M := by
    refine ⟨?_, (isPrimary_coord p).mp (by simpa only [hp] using β.2.1)⟩
    have hn := norm_coord_rational p
    rw [hp, hM] at hn
    exact_mod_cast hn.symm
  have hpair := Cubic.BoxAsymptotic.LocalTraceAtThree.primary_pair hprimary
  obtain ⟨a, ha⟩ := hpair.2.2.1.dvd
  obtain ⟨b, hb⟩ := hpair.2.2.2.dvd
  let α : E := (β.1 : E) / M
  have hα0 : α ≠ 0 := div_ne_zero (primary_ne_zero β) hM0
  have hn : Algebra.norm ℚ α = M := by
    apply (algebraMap ℚ E).injective
    rw [norm_eq_mul_conjugation]
    simp only [α, map_div₀, map_natCast, div_mul_div_comm,
      ← norm_eq_mul_conjugation, hM, map_pow]
    field_simp
  have ht : Algebra.trace ℚ E α = (2 * p.1 - p.2 : ℤ) / (M : ℚ) := by
    apply (algebraMap ℚ E).injective
    rw [trace_eq_add_conjugation]
    simp only [α, map_div₀, map_natCast]
    rw [← add_div, ← trace_eq_add_conjugation, ← hp, trace_coord_rational]
  let P := parameterEquiv.symm (Units.mk0 α hα0)
  have he : (parameterEquiv P : E) = α := by simp [P]
  have hi : AffineInvariantRing.IntegralPoint P := by
    rw [Cubic.PoissonSummation.IntegralPointComparison.coefficient_criterion P]
    constructor
    · refine ⟨-a, ?_⟩
      rw [linearCoefficient_eq, he, hn]
      have ha' : (M : ℚ) - 1 = 3 * (a : ℚ) := by exact_mod_cast ha
      push_cast
      linarith
    · refine ⟨b, ?_⟩
      rw [constantCoefficient_eq, he, hn, ht]
      have hb' : 3 * (M : ℚ) - 1 - ((2 * p.1 - p.2 : ℤ) : ℚ) = 27 * b := by
        exact_mod_cast hb
      field_simp
      linear_combination hb'
  refine ⟨⟨P, hi⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change ((toPrimary ⟨P, hi⟩).1 : E) = (β.1 : E)
  rw [toPrimary_val ⟨P, hi⟩]
  change algebraMap ℚ E (Algebra.norm ℚ (parameterEquiv P : E)) *
    (parameterEquiv P : E) = _
  rw [he, hn, map_natCast]
  dsimp [α]
  field_simp

def pointEquiv : IntegralTorus ≃ PrimaryCubes :=
  Equiv.ofBijective toPrimary ⟨toPrimary_injective, toPrimary_surjective⟩

def affineEquiv : IntegralTorus ≃ IntegralAffine :=
  Equiv.ofBijective (fun P => ⟨restrictPoint P.1, P.2⟩)
    ⟨fun P Q h => Subtype.ext (restrict_injective (congrArg Subtype.val h)), by
      intro P
      obtain ⟨Q, hQ, -⟩ := exists_unique_integral_extension P.1 P.2
      have hi : AffineInvariantRing.IntegralPoint Q := by
        change AffineChartInvariants.IsD0Integral (restrictPoint Q)
        rw [hQ]
        exact P.2
      exact ⟨⟨Q, hi⟩, Subtype.ext hQ⟩⟩

theorem norm_height (P : IntegralTorus) :
    (Algebra.norm ℚ ((pointEquiv P).1 : E) : ℝ) = pointHeight P ^ 6 := by
  rw [show ((pointEquiv P).1 : E) = pointResolvent P.1 from toPrimary_val P,
    pointResolvent, norm_resolvent, norm_parameter]
  have hh := CanonicalHeight.«prop:canonicalHeight».2 P.1 P.2
  have hn := CanonicalHeight.norm_ge_one P.1 P.2
  simp only [pointHeight, hh, Complex.ofReal_re]
  push_cast
  rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, Real.sq_sqrt (by linarith)]

end Cubic.Introduction.IntegralEisenstein
