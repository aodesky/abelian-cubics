import Cubic.SurfaceGeometry.DiagonalCubicData

noncomputable section

namespace Cubic.SurfaceGeometry.DiagonalCubicRelations

open MvPolynomial DiagonalCubicData
open Cubic.QuadraticCorrespondence.CyclotomicField

theorem substitution_monomial (d : Fin 4 →₀ ℕ) (r : E) :
    substitution (monomial d r) = monomial (substituteExponent d) r := by
  rw [substitution,aeval_monomial,Finsupp.prod_fintype]
  · simp only [Fin.prod_univ_succ,Fin.prod_univ_zero,mul_one]
    change C r * ((X 0*X 1*X 2)^d 0 * ((X 0^3)^d 1 * ((X 1^3)^d 2 * (X 2^3)^d 3))) = _
    simp only [mul_pow,X_pow_eq_monomial,monomial_pow,monomial_mul,one_pow,
      C_mul_monomial,mul_one]
    apply congrArg (fun e : Fin 3 →₀ ℕ => monomial e r)
    ext i
    fin_cases i <;> simp [substituteExponent] <;> omega
  · intro i
    simp

theorem substitution_mapDomain (p : FourVariables) :
    substitution p = Finsupp.mapDomain substituteExponent p := by
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => rw [map_add,Finsupp.mapDomain_add,hp,hq]
  | monomial d r => rw [substitution_monomial]; exact Finsupp.mapDomain_single.symm

theorem reduced_exponents_injective : Set.InjOn substituteExponent {d | d 0 < 3} := by
  intro d hd e he h
  simp only [Set.mem_setOf_eq] at hd he
  have h0 := congrArg (fun x => x 0) h
  have h1 := congrArg (fun x => x 1) h
  have h2 := congrArg (fun x => x 2) h
  simp [substituteExponent] at h0 h1 h2
  ext i
  fin_cases i <;> simp <;> omega

theorem reduced_substitution_injective {p q : FourVariables}
    (hp : degreeOf 0 p < 3) (hq : degreeOf 0 q < 3)
    (h : substitution p = substitution q) : p = q := by
  rw [substitution_mapDomain,substitution_mapDomain] at h
  apply Finsupp.mapDomain_injOn {d : Fin 4 →₀ ℕ | d 0 < 3}
    reduced_exponents_injective ?_ ?_ h
  · intro d hd
    exact lt_of_le_of_lt (monomial_le_degreeOf 0 hd) hp
  · intro d hd
    exact lt_of_le_of_lt (monomial_le_degreeOf 0 hd) hq

theorem substitution_via_finSucc (p : FourVariables) :
    substitution p = polynomialSubstitution (finSuccEquiv E 3 p) := by
  have h : substitution = polynomialSubstitution.comp (finSuccEquiv E 3).toAlgHom := by
    ext i : 1
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [substitution,polynomialSubstitution,coefficientSubstitution,finSuccEquiv_X_zero]
    · simp [substitution,polynomialSubstitution,coefficientSubstitution,finSuccEquiv_X_succ]
  exact DFunLike.congr_fun h p

theorem relation_degree : Polynomial.IsMonicOfDegree relation 3 := by
  exact (Polynomial.isMonicOfDegree_X_pow Ternary 3).sub
    (by simp only [Polynomial.natDegree_C]; omega)

theorem relation_root : polynomialSubstitution relation = 0 := by
  simp [polynomialSubstitution,relation,coefficientSubstitution]
  ring

theorem relations_iff (p : Polynomial Ternary) :
    polynomialSubstitution p = 0 ↔ relation ∣ p := by
  constructor
  · intro hp
    have hne : relation ≠ 1 := by
      intro h
      have hd := relation_degree.natDegree_eq
      rw [h,Polynomial.natDegree_one] at hd
      contradiction
    have hd := Polynomial.natDegree_modByMonic_lt p relation_degree.monic hne
    rw [relation_degree.natDegree_eq] at hd
    have hv := Polynomial.eval₂_modByMonic_eq_self_of_root
      (p := p) relation_degree.monic relation_root
    change polynomialSubstitution (p %ₘ relation) = polynomialSubstitution p at hv
    rw [hp] at hv
    have hz : (finSuccEquiv E 3).symm (p %ₘ relation) = 0 := by
      apply reduced_substitution_injective
      · rw [← natDegree_finSuccEquiv,AlgEquiv.apply_symm_apply]
        exact hd
      · simp
      · rw [substitution_via_finSucc,AlgEquiv.apply_symm_apply,hv,map_zero]
    have hr : p %ₘ relation = 0 := (finSuccEquiv E 3).symm.injective (by simpa using hz)
    exact (Polynomial.modByMonic_eq_zero_iff_dvd relation_degree.monic).mp hr
  · rintro ⟨q,rfl⟩
    rw [map_mul,relation_root,zero_mul]

theorem relation_finSucc : finSuccEquiv E 3 multivariateRelation = relation := by
  have h1 : finSuccEquiv E 3 (X 1) = Polynomial.C (X 0) := finSuccEquiv_X_succ (j := 0)
  have h2 : finSuccEquiv E 3 (X 2) = Polynomial.C (X 1) := finSuccEquiv_X_succ (j := 1)
  have h3 : finSuccEquiv E 3 (X 3) = Polynomial.C (X 2) := finSuccEquiv_X_succ (j := 2)
  simp only [multivariateRelation,relation,map_sub,map_pow,map_mul,finSuccEquiv_X_zero,h1,h2,h3]

theorem multivariate_relations_iff (p : FourVariables) :
    substitution p = 0 ↔ multivariateRelation ∣ p := by
  rw [substitution_via_finSucc,relations_iff]
  constructor
  · rintro ⟨q,hq⟩
    refine ⟨(finSuccEquiv E 3).symm q,(finSuccEquiv E 3).injective ?_⟩
    rw [map_mul,relation_finSucc,AlgEquiv.apply_symm_apply,hq]
  · rintro ⟨q,rfl⟩
    exact ⟨finSuccEquiv E 3 q,by rw [map_mul,relation_finSucc]⟩

end Cubic.SurfaceGeometry.DiagonalCubicRelations
