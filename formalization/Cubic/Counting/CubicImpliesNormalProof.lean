import CubicTargets.Counting.CubicImpliesNormalTarget
import Cubic.Counting.CubicImpliesNormal
import Cubic.Counting.CyclicPolynomialRealRoots
import Mathlib.RingTheory.Trace.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.FieldTheory.IntermediateField.Algebraic

/-!
# Proof of `lemma:cubicimpliesnormal`

The paper's proof: let `σ` generate `C₃`; complex conjugation acts trivially in a
Galois group of order three, so the roots are real; the three embeddings identify
`ℚ(x) ⊗ ℝ` with `ℝ³`, so `x` is normal iff the circulant determinant of `(x, σx, σ²x)`
is nonzero; it equals `-(x+y+z)/2 · Σ(x-y)²`, nonzero since the trace is nonzero
(`t²`-coefficient `-1`) and the roots are distinct.

Correspondence with the Lean proof:
* `f` has degree three and `ℚ(x)` is its splitting field in `ℂ` (`natDegree_eq_three`,
  `adjoin_eq_splitField`); hence `ℚ(x)/ℚ` is Galois with three automorphisms. The paper
  takes these facts for granted.
* The roots are real: `CyclicPolynomialRealRoots.root_im_zero` (complex conjugation
  restricts to an element of order `≤ 2` of a group of order three). Hence every element
  of `ℚ(x)` is real (`im_eq_zero`) and taking real parts is a ring map `ℚ(x) → ℝ`.
* The trace of `x` is `-(t²-coefficient)/(leading coefficient) ≠ 0` (`trace_gen`).
  The polynomial is not assumed monic.
* The determinant step is `C3Algebra.normal_of_real`, which uses the factorization
  `eqn:normalityDeterminant` through `Normality.linearIndependent_conjugates_of_trace_one`.
  Distinctness of `x` and `σx` holds because `σ ≠ 1` and `x` generates `ℚ(x)`.
-/

noncomputable section

namespace Cubic.Counting.CubicImpliesNormalProof

open Polynomial IntermediateField Module
open Cubic.QuadraticCorrespondence.CorrespondencePolynomials
open Cubic.OrbitParametrization.C3Algebra

variable {f : ℚ[X]} {x : ℂ}

theorem isIntegral_of_root (hirr : Irreducible f) (hx : aeval x f = 0) : IsIntegral ℚ x :=
  IsAlgebraic.isIntegral ⟨f, hirr.ne_zero, hx⟩

/-- The minimal polynomial of `x` is `f` divided by its leading coefficient. -/
theorem minpoly_eq (hirr : Irreducible f) (hx : aeval x f = 0) :
    minpoly ℚ x = f * C f.leadingCoeff⁻¹ :=
  (minpoly.eq_of_irreducible hirr hx).symm

theorem finrank_adjoin (hirr : Irreducible f) (hx : aeval x f = 0) :
    finrank ℚ ℚ⟮x⟯ = f.natDegree := by
  rw [adjoin.finrank (isIntegral_of_root hirr hx), minpoly_eq hirr hx,
    natDegree_mul_C (inv_ne_zero (leadingCoeff_ne_zero.mpr hirr.ne_zero))]

/-- The splitting field of `f` inside `ℂ`. -/
abbrev splitField (f : ℚ[X]) : IntermediateField ℚ ℂ := adjoin ℚ (f.rootSet ℂ)

theorem isSplittingField (f : ℚ[X]) : f.IsSplittingField ℚ (splitField f) :=
  adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)

instance (f : ℚ[X]) : FiniteDimensional ℚ (splitField f) :=
  haveI := isSplittingField f
  IsSplittingField.finiteDimensional _ f

theorem finrank_splitField (hc : HasCyclicCubicGaloisGroup f) :
    finrank ℚ (splitField f) = 3 := by
  haveI := isSplittingField f
  haveI : Normal ℚ (splitField f) := Normal.of_isSplittingField f
  haveI : IsGalois ℚ (splitField f) := isGalois_iff.mpr ⟨inferInstance, inferInstance⟩
  rw [← IsGalois.card_aut_eq_finrank]
  obtain ⟨e⟩ := hc
  rw [Nat.card_congr ((AlgEquiv.autCongr (IsSplittingField.algEquiv _ f)).toEquiv.trans
    e.toEquiv)]
  simp

theorem adjoin_le_splitField (hirr : Irreducible f) (hx : aeval x f = 0) :
    ℚ⟮x⟯ ≤ splitField f := by
  rw [adjoin_simple_le_iff]
  exact subset_adjoin _ _ (mem_rootSet.mpr ⟨hirr.ne_zero, hx⟩)

/-- Irreducibility and Galois group `C₃` force degree three. -/
theorem natDegree_eq_three (hirr : Irreducible f) (hc : HasCyclicCubicGaloisGroup f)
    (hx : aeval x f = 0) : f.natDegree = 3 := by
  have hdvd := finrank_dvd_of_le_right (adjoin_le_splitField hirr hx)
  rw [finrank_adjoin hirr hx, finrank_splitField hc] at hdvd
  have h1 : f.natDegree ≠ 1 := by
    intro h1
    obtain ⟨e⟩ := hc
    haveI := Gal.uniqueGalOfSplits _ (Splits.of_natDegree_le_one h1.le)
    have h3 : Fintype.card f.Gal = 3 := by rw [Fintype.card_congr e.toEquiv]; rfl
    rw [Fintype.card_unique] at h3
    exact absurd h3 (by norm_num)
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
  · exact absurd h h1
  · exact h

/-- `ℚ(x)` is the splitting field of `f` in `ℂ`. -/
theorem adjoin_eq_splitField (hirr : Irreducible f) (hc : HasCyclicCubicGaloisGroup f)
    (hx : aeval x f = 0) : ℚ⟮x⟯ = splitField f :=
  eq_of_le_of_finrank_eq (adjoin_le_splitField hirr hx) (by
    rw [finrank_adjoin hirr hx, finrank_splitField hc, natDegree_eq_three hirr hc hx])

theorem isGalois_adjoin (hirr : Irreducible f) (hc : HasCyclicCubicGaloisGroup f)
    (hx : aeval x f = 0) : IsGalois ℚ ℚ⟮x⟯ := by
  haveI : f.IsSplittingField ℚ ℚ⟮x⟯ := by
    rw [adjoin_eq_splitField hirr hc hx]
    exact isSplittingField f
  haveI : FiniteDimensional ℚ ℚ⟮x⟯ := IsSplittingField.finiteDimensional _ f
  haveI : Normal ℚ ℚ⟮x⟯ := Normal.of_isSplittingField f
  exact isGalois_iff.mpr ⟨inferInstance, inferInstance⟩

/-- The roots are real, so every element of `ℚ(x)` is real. -/
theorem im_eq_zero (hirr : Irreducible f) (hc : HasCyclicCubicGaloisGroup f)
    (hx : aeval x f = 0) (z : ℚ⟮x⟯) : (z : ℂ).im = 0 := by
  have hxim : x.im = 0 :=
    CyclicPolynomialRealRoots.root_im_zero hc ⟨x, mem_rootSet.mpr ⟨hirr.ne_zero, hx⟩⟩
  have hle : ℚ⟮x⟯ ≤ (IsScalarTower.toAlgHom ℚ ℝ ℂ).fieldRange := by
    rw [adjoin_simple_le_iff]
    exact ⟨x.re, Complex.ext (by simp) (by simp [hxim])⟩
  obtain ⟨r, hr⟩ := hle z.2
  rw [← hr]
  simp

/-- Taking real parts is a ring map `ℚ(x) → ℝ`, since `ℚ(x) ⊆ ℝ`. -/
def realPart (hirr : Irreducible f) (hc : HasCyclicCubicGaloisGroup f)
    (hx : aeval x f = 0) : ℚ⟮x⟯ →+* ℝ where
  toFun z := (z : ℂ).re
  map_one' := by simp
  map_mul' z w := by
    simp [Complex.mul_re, im_eq_zero hirr hc hx z, im_eq_zero hirr hc hx w]
  map_zero' := by simp
  map_add' z w := by simp

/-- The trace of `x` is `-(t²-coefficient)/(leading coefficient) = 1/(leading coefficient)`. -/
theorem trace_gen (hirr : Irreducible f) (hc : HasCyclicCubicGaloisGroup f)
    (hcoeff : f.coeff 2 = -1) (hx : aeval x f = 0) :
    Algebra.trace ℚ ℚ⟮x⟯ (AdjoinSimple.gen ℚ x) = f.leadingCoeff⁻¹ := by
  have hlc : f.leadingCoeff⁻¹ ≠ 0 := inv_ne_zero (leadingCoeff_ne_zero.mpr hirr.ne_zero)
  rw [trace_adjoinSimpleGen (isIntegral_of_root hirr hx), minpoly_eq hirr hx, nextCoeff,
    natDegree_mul_C hlc, natDegree_eq_three hirr hc hx, if_neg (by norm_num), coeff_mul_C,
    show 3 - 1 = 2 from rfl, hcoeff]
  ring

theorem aut_eq_one_of_fixes (τ : ℚ⟮x⟯ ≃ₐ[ℚ] ℚ⟮x⟯) (hτ : τ (AdjoinSimple.gen ℚ x) =
    AdjoinSimple.gen ℚ x) : τ = 1 := by
  have h : τ.toAlgHom = (1 : ℚ⟮x⟯ ≃ₐ[ℚ] ℚ⟮x⟯).toAlgHom := by
    apply algHom_ext_of_eq_adjoin (S := ℚ⟮x⟯) (s := {x}) (hS := rfl)
    intro y hy
    obtain rfl : y = x := hy
    exact hτ
  exact AlgEquiv.ext fun z => congrArg (fun φ : ℚ⟮x⟯ →ₐ[ℚ] ℚ⟮x⟯ => φ z) h

/-- `lemma:cubicimpliesnormal`. -/
theorem «lemma:cubicimpliesnormal» : CubicTargets.Counting.CubicImpliesNormal.Claim := by
  intro f x hirr hc hcoeff hx
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI hgal := isGalois_adjoin hirr hc hx
  haveI : FiniteDimensional ℚ ℚ⟮x⟯ := adjoin.finiteDimensional (isIntegral_of_root hirr hx)
  refine ⟨hgal, ?_⟩
  have hfin : finrank ℚ ℚ⟮x⟯ = 3 := by
    rw [finrank_adjoin hirr hx, natDegree_eq_three hirr hc hx]
  -- an identification of `Aut(ℚ(x)/ℚ)` with `C₃`
  let e : (ℚ⟮x⟯ ≃ₐ[ℚ] ℚ⟮x⟯) ≃* C3 :=
    mulEquivOfPrimeCardEq (by rw [IsGalois.card_aut_eq_finrank, hfin])
      (by rw [Nat.card_eq_fintype_card]; rfl)
  let A : C3Alg :=
    { carrier := ℚ⟮x⟯
      commRing := (inferInstance : CommRing ℚ⟮x⟯)
      algebra := (inferInstance : Algebra ℚ ℚ⟮x⟯)
      act := e.symm.toMonoidHom
      model := Or.inl ⟨Field.toIsField _, hfin, e.symm.injective⟩ }
  let ι := realPart hirr hc hx
  set θ := AdjoinSimple.gen ℚ x
  have htrace : traceSum A θ = algebraMap ℚ ℚ⟮x⟯ f.leadingCoeff⁻¹ := by
    change ∑ g : C3, e.symm g θ = _
    rw [e.symm.bijective.sum_comp (fun τ => τ θ), ← trace_eq_sum_automorphisms,
      trace_gen hirr hc hcoeff hx]
  have htr : ι (traceSum A θ) ≠ 0 := by
    rw [htrace, ← RingHom.comp_apply]
    exact (map_ne_zero_iff _ (ι.comp (algebraMap ℚ ℚ⟮x⟯)).injective).mpr
      (inv_ne_zero (leadingCoeff_ne_zero.mpr hirr.ne_zero))
  have hne : ι θ ≠ ι (A.act σ θ) := by
    intro h
    have h1 := aut_eq_one_of_fixes _ (ι.injective h).symm
    have h2 : e.symm σ = e.symm 1 := h1.trans (map_one e.symm).symm
    exact absurd (e.symm.injective h2) (by decide)
  have hn := normal_of_real A ι θ htr hne
  exact (linearIndependent_equiv e.symm.toEquiv).mp hn

end Cubic.Counting.CubicImpliesNormalProof
