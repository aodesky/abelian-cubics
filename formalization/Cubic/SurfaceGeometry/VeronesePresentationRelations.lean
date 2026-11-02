import Cubic.SurfaceGeometry.VeronesePresentationData

noncomputable section

namespace Cubic.SurfaceGeometry.VeronesePresentationRelations

open MvPolynomial InvariantCubicData VeronesePresentationData
open Cubic.ToricHeights.TernaryCyclicInvariants

theorem quadratic_degree : Polynomial.IsMonicOfDegree quadratic 2 := by
  exact Polynomial.isMonicOfDegree_sub_add_two _ _

theorem coefficientEvaluation_X (i : Fin 4) :
    coefficientEvaluation (X i) = ![B, A, e 2 ^ 3, InvariantCubicData.C] i := by
  fin_cases i <;> simp [coefficientEvaluation, symmetricEval,
    SymmetricVeroneseRelations.substitution, A, B, InvariantCubicData.C]

theorem evaluation_C (a : Coefficients) : evaluation (Polynomial.C a) = coefficientEvaluation a :=
  Polynomial.eval₂_C _ _

theorem evaluation_X : evaluation Polynomial.X = delta := Polynomial.eval₂_X _ _

theorem quadratic_root : evaluation quadratic = 0 := by
  have h := SurfaceInvariantRelation.«eqn:surfaceInvariantRelation»
  unfold CubicTargets.SurfaceGeometry.SurfaceInvariantRelation.Claim at h
  simp only [quadratic, map_add, map_sub, map_mul, map_pow, map_ofNat,
    evaluation_C, evaluation_X, coefficientEvaluation_X]
  dsimp [A, B, InvariantCubicData.C]
  linear_combination h

theorem symmetric_root : evaluation symmetricRelation = 0 := by
  simp only [symmetricRelation, evaluation_C,
    SymmetricVeroneseRelations.multivariateRelation, map_sub, map_pow, map_mul,
    coefficientEvaluation_X]
  dsimp [A, B, InvariantCubicData.C]
  ring

theorem kernel : RingHom.ker evaluation.toRingHom = relations := by
  apply le_antisymm
  · intro p hp
    have hp' : evaluation p = 0 := hp
    have hne : quadratic ≠ 1 := by
      intro he
      have hd := quadratic_degree.natDegree_eq
      rw [he, Polynomial.natDegree_one] at hd
      contradiction
    have hd := Polynomial.natDegree_modByMonic_lt p quadratic_degree.monic hne
    rw [quadratic_degree.natDegree_eq] at hd
    obtain ⟨b,a,he⟩ := Polynomial.exists_eq_X_add_C_of_natDegree_le_one
      (show (p %ₘ quadratic).natDegree ≤ 1 by omega)
    have hv := Polynomial.eval₂_modByMonic_eq_self_of_root
      (p := p) quadratic_degree.monic quadratic_root
    change evaluation (p %ₘ quadratic) = evaluation p at hv
    rw [hp', he] at hv
    rw [map_add, map_mul, evaluation_C, evaluation_C, evaluation_X] at hv
    have hn : normalForm (SymmetricVeroneseRelations.substitution a,
        SymmetricVeroneseRelations.substitution b) = normalForm (0,0) := by
      simp only [normalForm, map_zero, zero_mul, zero_add]
      change coefficientEvaluation a + coefficientEvaluation b * delta = 0
      linear_combination hv
    have hab := IntegralInvariantNormalForm.normalForm_injective hn
    obtain ⟨a',ha⟩ := (SymmetricVeroneseRelations.multivariate_relations_iff a).mp
      (congrArg Prod.fst hab)
    obtain ⟨b',hb⟩ := (SymmetricVeroneseRelations.multivariate_relations_iff b).mp
      (congrArg Prod.snd hab)
    have hs : symmetricRelation ∈ relations := Ideal.subset_span (by simp)
    have hq : quadratic ∈ relations := Ideal.subset_span (by simp)
    have hr : p %ₘ quadratic ∈ relations := by
      rw [he, ha, hb, map_mul, map_mul]
      exact relations.add_mem
        (relations.mul_mem_right Polynomial.X (relations.mul_mem_right (Polynomial.C b') hs))
        (relations.mul_mem_right (Polynomial.C a') hs)
    rw [← Polynomial.modByMonic_add_div p quadratic_degree.monic]
    exact relations.add_mem hr (relations.mul_mem_right _ hq)
  · rw [relations, Ideal.span_le]
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl
    · exact symmetric_root
    · exact quadratic_root

end Cubic.SurfaceGeometry.VeronesePresentationRelations
