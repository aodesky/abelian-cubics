import Cubic.SantensComparison.RegularFunctions
import Cubic.SantensComparison.ToricMetricData
import Cubic.SurfaceGeometry.AffineInvariantPresentation
import Cubic.ToricHeights.AffinePointComparison
import Mathlib.RingTheory.Adjoin.FG

/-! The generic fibre of the original integral model, in the actual quotient
torus characters, is the semigroup algebra of the original affine cone.
The comparison uses all three integral invariants, including the oriented
invariant δ; the two cubic coefficients alone do not generate this algebra. -/

noncomputable section

namespace Cubic.SantensComparison.AffineConeAlgebra

open Cubic.QuadraticCorrespondence
open CyclotomicField CyclotomicTorusGalois
open Cubic.ToricHeights Cubic.SurfaceGeometry
open DescendedCoefficients RationalCoefficientFormula DescendedCyclicInvariant
open RegularFunctions ToricMetricData

def expansion : quotientFixedRing →ₐ[ℚ] CoverRing :=
  coverFixedRing.val.comp fixedRingEquiv.symm.toAlgHom

def coneInclusion : AddMonoidAlgebra E openCharacters →ₐ[E] CoverRing :=
  AddMonoidAlgebra.mapDomainAlgHom E E openCharacters.subtype

def coneAlgebra : Subalgebra E CoverRing := coneInclusion.range

def genericFibre : Subalgebra E CoverRing :=
  Algebra.adjoin E (expansion '' (paperModel : Set quotientFixedRing))

theorem coneInclusion_injective : Function.Injective coneInclusion :=
  Finsupp.mapDomain_injective Subtype.val_injective

theorem expansion_linear : expansion linearCoefficient = linearExpression := by
  rw [← linearExpression_image]
  change ((fixedRingEquiv.symm (fixedRingEquiv _)) : CoverRing) = _
  rw [AlgEquiv.symm_apply_apply]

theorem expansion_constant : expansion constantCoefficient = constantExpression := by
  rw [← constantExpression_image]
  change ((fixedRingEquiv.symm (fixedRingEquiv _)) : CoverRing) = _
  rw [AlgEquiv.symm_apply_apply]

theorem expansion_delta : expansion delta = AffinePointParameter.deltaExpression :=
  AffinePointParameter.deltaExpression_inverse

def normMonomial : CoverRing := AddMonoidAlgebra.single (1,1) 1
def firstMonomial : CoverRing := AddMonoidAlgebra.single (2,1) 1
def secondMonomial : CoverRing := AddMonoidAlgebra.single (1,2) 1

theorem character_inequalities (m : ℤ × ℤ) :
    m ∈ openCharacters ↔ 0 ≤ 2*m.1-m.2 ∧ 0 ≤ 2*m.2-m.1 := by
  constructor
  · intro h
    have h₀ := h 0
    have h₁ := h 1
    simpa [FanData.pairing, FanData.openRay, ResolutionData.rays, mul_comm, sub_eq_add_neg,
      add_comm] using And.intro h₀ h₁
  · rintro ⟨ha,hb⟩ i
    fin_cases i <;>
      norm_num [FanData.pairing, FanData.openRay, ResolutionData.rays] <;> omega

theorem single_mem_cone (m : openCharacters) (c : E) :
    AddMonoidAlgebra.single m.val c ∈ coneAlgebra := by
  refine ⟨AddMonoidAlgebra.single m c, ?_⟩
  simp [coneInclusion, AddMonoidAlgebra.mapDomainAlgHom]

theorem monomials_mem_cone : normMonomial ∈ coneAlgebra ∧
    firstMonomial ∈ coneAlgebra ∧ secondMonomial ∈ coneAlgebra := by
  refine ⟨single_mem_cone ⟨(1,1),?_⟩ 1,
    single_mem_cone ⟨(2,1),?_⟩ 1, single_mem_cone ⟨(1,2),?_⟩ 1⟩ <;>
    rw [character_inequalities] <;> norm_num

theorem expressions_mem_cone : linearExpression ∈ coneAlgebra ∧
    constantExpression ∈ coneAlgebra ∧ AffinePointParameter.deltaExpression ∈ coneAlgebra := by
  obtain ⟨hn,hf,hg⟩ := monomials_mem_cone
  have ha : linearExpression ∈ coneAlgebra :=
    (coneAlgebra.restrictScalars ℚ).smul_mem (coneAlgebra.sub_mem coneAlgebra.one_mem hn) _
  have hb : constantExpression ∈ coneAlgebra :=
    (coneAlgebra.restrictScalars ℚ).smul_mem
      (coneAlgebra.sub_mem (coneAlgebra.sub_mem
        (coneAlgebra.sub_mem (coneAlgebra.mul_mem (coneAlgebra.natCast_mem 3) hn) hf) hg)
          coneAlgebra.one_mem) _
  refine ⟨ha,hb,?_⟩
  exact coneAlgebra.add_mem
    ((coneAlgebra.restrictScalars ℚ).smul_mem
      (coneAlgebra.add_mem ha (coneAlgebra.mul_mem (coneAlgebra.natCast_mem 3) hb)) _)
    (coneAlgebra.smul_mem (coneAlgebra.sub_mem hf hg) _)

def modelEvaluation : MvPolynomial (Fin 3) ℤ →ₐ[ℤ] quotientFixedRing :=
  AffineInvariantRing.invariantRestriction.comp AffineInvariantPresentation.evaluation

theorem modelEvaluation_X (i : Fin 3) :
    modelEvaluation (MvPolynomial.X i)=![linearCoefficient,constantCoefficient,delta] i := by
  change AffineInvariantRing.invariantRestriction
    ⟨(MvPolynomial.aeval ![AffineChartInvariants.e2,-AffineChartInvariants.e3,
      AffineChartInvariants.delta]) (MvPolynomial.X i),_⟩ = _
  simp only [MvPolynomial.aeval_X]
  fin_cases i
  · exact AffineInvariantRing.invariantRestriction_linear
  · exact AffineInvariantRing.invariantRestriction_constant
  · exact AffinePointComparison.invariantRestriction_delta

theorem modelEvaluation_eq : modelEvaluation =
    MvPolynomial.aeval ![linearCoefficient,constantCoefficient,delta] := by
  apply MvPolynomial.algHom_ext
  intro i
  simpa using modelEvaluation_X i

theorem modelEvaluation_range : modelEvaluation.range = paperModel := by
  ext f
  constructor
  · rintro ⟨p,rfl⟩
    exact ⟨AffineInvariantPresentation.evaluation p,rfl⟩
  · rintro ⟨p,rfl⟩
    obtain ⟨q,rfl⟩ := AffineInvariantPresentation.evaluation_surjective p
    exact ⟨q,rfl⟩

theorem paperModel_generators : paperModel =
    Algebra.adjoin ℤ {linearCoefficient,constantCoefficient,delta} := by
  rw [← modelEvaluation_range, modelEvaluation_eq, ← Algebra.adjoin_range_eq_range_aeval]
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

theorem paperModel_finite_generation : paperModel.FG := by
  classical
  exact ⟨{linearCoefficient,constantCoefficient,delta},by
    simpa using paperModel_generators.symm⟩

theorem expansion_evaluation : (expansion.restrictScalars ℤ).comp modelEvaluation =
    MvPolynomial.aeval ![linearExpression,constantExpression,AffinePointParameter.deltaExpression] := by
  ext i
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, modelEvaluation_X,
    MvPolynomial.aeval_X]
  fin_cases i <;> simp [expansion_linear, expansion_constant, expansion_delta]

theorem genericFibre_le_cone : genericFibre ≤ coneAlgebra := by
  apply Algebra.adjoin_le
  rintro _ ⟨f,hf,rfl⟩
  rw [← modelEvaluation_range] at hf
  obtain ⟨p,rfl⟩ := hf
  have he := congrArg (fun e : MvPolynomial (Fin 3) ℤ →ₐ[ℤ] CoverRing => e p)
    expansion_evaluation
  change expansion (modelEvaluation p)=_ at he
  change expansion (modelEvaluation p) ∈ coneAlgebra
  rw [he]
  have hr : (MvPolynomial.aeval
      ![linearExpression,constantExpression,AffinePointParameter.deltaExpression]).range ≤
        coneAlgebra.restrictScalars ℤ := by
    rw [← Algebra.adjoin_range_eq_range_aeval]
    apply Algebra.adjoin_le
    rintro _ ⟨i,rfl⟩
    fin_cases i
    · exact expressions_mem_cone.1
    · exact expressions_mem_cone.2.1
    · exact expressions_mem_cone.2.2
  exact hr ⟨p,rfl⟩

theorem expressions_mem_generic : linearExpression ∈ genericFibre ∧
    constantExpression ∈ genericFibre ∧ AffinePointParameter.deltaExpression ∈ genericFibre := by
  have h (i : Fin 3) : expansion (modelEvaluation (MvPolynomial.X i)) ∈ genericFibre :=
    Algebra.subset_adjoin ⟨_,modelEvaluation_range ▸ ⟨_,rfl⟩,rfl⟩
  simpa [modelEvaluation_X, expansion_linear, expansion_constant, expansion_delta] using
      And.intro (h 0) (And.intro (h 1) (h 2))

theorem monomials_mem_generic : normMonomial ∈ genericFibre ∧
    firstMonomial ∈ genericFibre ∧ secondMonomial ∈ genericFibre := by
  obtain ⟨ha,hb,hd⟩ := expressions_mem_generic
  have hn : normMonomial = 1-(3:ℚ) • linearExpression := by
    change normMonomial = 1-(3:ℚ) • ((1/3:ℚ) • (1-normMonomial))
    rw [smul_smul]
    norm_num
  have hn' : normMonomial ∈ genericFibre := hn ▸ genericFibre.sub_mem
    genericFibre.one_mem ((genericFibre.restrictScalars ℚ).smul_mem ha 3)
  have hsum : firstMonomial+secondMonomial =
      (3:ℚ) • normMonomial-1-(27:ℚ) • constantExpression := by
    change firstMonomial+secondMonomial = (3:ℚ) • normMonomial-1-
      (27:ℚ) • ((1/27:ℚ) • (3*normMonomial-firstMonomial-secondMonomial-1))
    rw [smul_smul, show (27:ℚ)*(1/27)=1 by norm_num, one_smul]
    rw [Algebra.smul_def, map_ofNat]
    ring
  have hsum' : firstMonomial+secondMonomial ∈ genericFibre := hsum ▸
    genericFibre.sub_mem
      (genericFibre.sub_mem ((genericFibre.restrictScalars ℚ).smul_mem hn' 3)
        genericFibre.one_mem) ((genericFibre.restrictScalars ℚ).smul_mem hb 27)
  have hdiff : firstMonomial-secondMonomial = (6*sqrtNegThree:E) •
      (AffinePointParameter.deltaExpression - (1/2:ℚ) •
        (linearExpression+3*constantExpression)) := by
    simp only [AffinePointParameter.deltaExpression, add_sub_cancel_left, smul_smul]
    rw [mul_inv_cancel₀ (mul_ne_zero (by norm_num) AffinePointParameter.sqrt_ne_zero), one_smul]
    rfl
  have hdiff' : firstMonomial-secondMonomial ∈ genericFibre := hdiff ▸
    genericFibre.smul_mem (genericFibre.sub_mem hd
      ((genericFibre.restrictScalars ℚ).smul_mem (genericFibre.add_mem ha
        (genericFibre.mul_mem (genericFibre.natCast_mem 3) hb)) _)) _
  have hf : firstMonomial = (1/2:ℚ) •
      ((firstMonomial+secondMonomial)+(firstMonomial-secondMonomial)) := by module
  have hg : secondMonomial = (1/2:ℚ) •
      ((firstMonomial+secondMonomial)-(firstMonomial-secondMonomial)) := by module
  exact ⟨hn',hf ▸ (genericFibre.restrictScalars ℚ).smul_mem
    (genericFibre.add_mem hsum' hdiff') _,
    hg ▸ (genericFibre.restrictScalars ℚ).smul_mem (genericFibre.sub_mem hsum' hdiff') _⟩

theorem character_decomposition (m : openCharacters) :
    ∃ a b c : ℕ, m.val = a • (1,1) + b • (2,1) + c • (1,2) := by
  have hm := (character_inequalities m.val).mp m.property
  by_cases h : m.val.2 ≤ m.val.1
  · refine ⟨(2*m.val.2-m.val.1).toNat,(m.val.1-m.val.2).toNat,0,?_⟩
    simp only [Prod.smul_mk, Prod.mk_add_mk, nsmul_eq_mul, mul_one]
    apply Prod.ext <;> dsimp <;> omega
  · refine ⟨(2*m.val.1-m.val.2).toNat,0,(m.val.2-m.val.1).toNat,?_⟩
    simp only [Prod.smul_mk, Prod.mk_add_mk, nsmul_eq_mul, mul_one]
    apply Prod.ext <;> dsimp <;> omega

theorem monomial_mem_generic (m : openCharacters) :
    AddMonoidAlgebra.single m.val (1:E) ∈ genericFibre := by
  obtain ⟨a,b,c,hm⟩ := character_decomposition m
  have he : AddMonoidAlgebra.single m.val (1:E) =
      normMonomial^a * firstMonomial^b * secondMonomial^c := by
    simp only [normMonomial, firstMonomial, secondMonomial, AddMonoidAlgebra.single_pow,
      one_pow, AddMonoidAlgebra.single_mul_single, one_mul, hm]
  rw [he]
  obtain ⟨hn,hf,hg⟩ := monomials_mem_generic
  exact genericFibre.mul_mem (genericFibre.mul_mem (genericFibre.pow_mem hn a)
    (genericFibre.pow_mem hf b)) (genericFibre.pow_mem hg c)

theorem cone_le_genericFibre : coneAlgebra ≤ genericFibre := by
  rintro _ ⟨p,rfl⟩
  change coneInclusion p ∈ genericFibre
  induction p using AddMonoidAlgebra.induction_on with
  | hM m =>
    simpa [coneInclusion, AddMonoidAlgebra.mapDomainAlgHom, AddMonoidAlgebra.of_apply] using
      monomial_mem_generic m
  | hadd x y hx hy => simpa only [map_add] using genericFibre.add_mem hx hy
  | hsmul r x hx => simpa only [map_smul] using genericFibre.smul_mem hx r

theorem generic_fibre : genericFibre = coneAlgebra :=
  le_antisymm genericFibre_le_cone cone_le_genericFibre

end Cubic.SantensComparison.AffineConeAlgebra
