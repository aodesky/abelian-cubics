import Cubic.SurfaceGeometry.VeroneseData

noncomputable section

namespace Cubic.SurfaceGeometry.SymmetricVeroneseGeneration

open MvPolynomial InvariantCubicData VeroneseGrading VeroneseData

theorem weight_formula (d : Fin 3 →₀ ℕ) :
    Finsupp.weight symmetricWeight d = ((d 0 + 2 * d 1 + 3 * d 2 : ℕ) : ZMod 3) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype]
  · simp [Fin.sum_univ_succ, symmetricWeight, nsmul_eq_mul]
    ring
  · intro i
    simp

theorem exponents_congruent (d : Fin 3 →₀ ℕ)
    (hd : Finsupp.weight symmetricWeight d = 0) : d 0 % 3 = d 1 % 3 := by
  rw [weight_formula, ZMod.natCast_eq_zero_iff] at hd
  obtain ⟨k,hk⟩ := hd
  omega

theorem monomial_normalForm (d : Fin 3 →₀ ℕ) (r : ℤ)
    (hd : Finsupp.weight symmetricWeight d = 0) :
    monomial d r = MvPolynomial.C r *
      ((X 0 ^ 3) ^ (d 0 / 3) * (X 0 * X 1) ^ (d 0 % 3) *
        (X 1 ^ 3) ^ (d 1 / 3) * X 2 ^ d 2) := by
  have hc := exponents_congruent d hd
  rw [mul_pow]
  simp only [X_pow_eq_monomial, monomial_pow, monomial_mul, one_pow, mul_one]
  rw [C_mul_monomial]
  simp only [mul_one]
  apply congrArg (fun e : Fin 3 →₀ ℕ => monomial e r)
  ext i
  fin_cases i <;> simp [hc] <;> omega

theorem generators_homogeneous : Algebra.adjoin ℤ symmetricGenerators ≤ symmetricVeronese := by
  rw [Algebra.adjoin_le_iff]
  intro p hp
  simp only [symmetricGenerators, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact (isWeightedHomogeneous_X (R := ℤ) symmetricWeight 0).pow 3
  · exact (isWeightedHomogeneous_X (R := ℤ) symmetricWeight 0).mul
      (isWeightedHomogeneous_X (R := ℤ) symmetricWeight 1)
  · exact isWeightedHomogeneous_X (R := ℤ) symmetricWeight 2
  · exact (isWeightedHomogeneous_X (R := ℤ) symmetricWeight 1).pow 3

theorem generated : Algebra.adjoin ℤ symmetricGenerators = symmetricVeronese := by
  apply le_antisymm generators_homogeneous
  intro p hp
  change IsWeightedHomogeneous symmetricWeight p 0 at hp
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero => exact (Algebra.adjoin ℤ symmetricGenerators).zero_mem
  | add p q hp hq ihp ihq => exact (Algebra.adjoin ℤ symmetricGenerators).add_mem ihp ihq
  | monomial d r hd =>
    rw [monomial_normalForm d r hd]
    let S := Algebra.adjoin ℤ symmetricGenerators
    have hA : X 0 ^ 3 ∈ S := Algebra.subset_adjoin (by simp [symmetricGenerators])
    have hB : X 0 * X 1 ∈ S := Algebra.subset_adjoin (by simp [symmetricGenerators])
    have hC : X 2 ∈ S := Algebra.subset_adjoin (by simp [symmetricGenerators])
    have hh : X 1 ^ 3 ∈ S := Algebra.subset_adjoin (by simp [symmetricGenerators])
    exact S.mul_mem (S.algebraMap_mem r)
      (S.mul_mem (S.mul_mem (S.mul_mem (S.pow_mem hA _) (S.pow_mem hB _))
        (S.pow_mem hh _)) (S.pow_mem hC _))

end Cubic.SurfaceGeometry.SymmetricVeroneseGeneration
