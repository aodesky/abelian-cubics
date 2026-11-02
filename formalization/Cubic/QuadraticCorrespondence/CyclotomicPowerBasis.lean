import Cubic.QuadraticCorrespondence.CyclotomicLocalAlgebra

/-!
# Coordinates in the cyclotomic quadratic algebra

The same power-basis coordinates work over local integers and residue fields.
The coordinate uniqueness proof uses the degree of the defining polynomial;
it does not assume that the quotient is a field.
-/

noncomputable section

namespace Cubic.QuadraticCorrespondence.CyclotomicLocalAlgebra

open Polynomial

variable {R : Type*} [CommRing R] [Nontrivial R]

def linear (a b : R) : Model R :=
  algebraMap R (Model R) a + algebraMap R (Model R) b * AdjoinRoot.root (cyclotomic 3 R)

theorem exists_linear (x : Model R) : ∃ a b : R, x = linear a b := by
  letI : Nontrivial (Model R) := nontrivial_of_ne (AdjoinRoot.mk _ 1) 0
    (AdjoinRoot.mk_ne_zero_of_natDegree_lt (cyclotomic.monic 3 R) one_ne_zero
      (by rw [natDegree_one, natDegree_cyclotomic]; decide))
  let pb := AdjoinRoot.powerBasis' (cyclotomic.monic 3 R)
  obtain ⟨f, hdeg, hf⟩ := pb.exists_eq_aeval x
  have hd : f.natDegree < 2 := by
    simpa only [pb, AdjoinRoot.powerBasis'_dim, natDegree_cyclotomic] using hdeg
  have he := f.eq_X_add_C_of_degree_le_one
    (degree_le_of_natDegree_le (Nat.le_of_lt_succ hd))
  refine ⟨f.coeff 0, f.coeff 1, ?_⟩
  rw [hf, he]
  simp [linear, pb, add_comm]

theorem linear_eq_zero_iff (a b : R) : linear a b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have hg : C b * X + C a = (0 : R[X]) := by
      by_contra hg
      have hd : (C b * X + C a).natDegree < (cyclotomic 3 R).natDegree := by
        rw [natDegree_add_C, natDegree_cyclotomic]
        have hd := natDegree_C_mul_X_pow_le b 1
        simp only [pow_one] at hd
        exact lt_of_le_of_lt hd (by decide)
      apply AdjoinRoot.mk_ne_zero_of_natDegree_lt (cyclotomic.monic 3 R) hg hd
      simpa [linear, map_add, map_mul, add_comm] using h
    exact ⟨by simpa using congrArg (fun f : R[X] => f.coeff 0) hg,
      by simpa using congrArg (fun f : R[X] => f.coeff 1) hg⟩
  · rintro ⟨rfl, rfl⟩
    simp [linear]

end Cubic.QuadraticCorrespondence.CyclotomicLocalAlgebra
