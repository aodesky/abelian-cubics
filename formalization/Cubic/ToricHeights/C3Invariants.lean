import Cubic.ToricHeights.CyclicSymmetricDecomposition
import CubicTargets.ToricHeights.C3Invariants

/-!
# `eqn:C3invariants`: `ℤ[X,Y,Z]^{C₃} = ℤ[e₁,e₂,e₃,X²Y+Y²Z+Z²X]`

The paper cites Campbell–Wehlau [Example 4.6] (the case `A₃ ≤ S₃` with secondary
invariants `1, Z(X²Y) = δ`). Following the matrix argument there, every invariant `f` is
`S + B·δ` with `S, B` symmetric (`CyclicSymmetricDecomposition.exists_symmetric_decomposition`;
the determinant of `[[1, δ], [1, τδ]]` is the Vandermonde product, and divisibility of
`f - τf` by it is proved over `ℤ`). The fundamental theorem of symmetric polynomials over `ℤ`
(`MvPolynomial.esymmAlgHom_surjective`) puts `S` and `B` in `ℤ[e₁,e₂,e₃]`.
-/

noncomputable section

namespace Cubic.ToricHeights.C3Invariants

open MvPolynomial TernaryCyclicInvariants CyclicSymmetricDecomposition

/-- Symmetric polynomials over `ℤ` lie in `ℤ[e₁,e₂,e₃]`. -/
theorem symmetric_mem_adjoin {p : TernaryRing} (hp : p.IsSymmetric) :
    p ∈ Algebra.adjoin ℤ ({e 1, e 2, e 3, delta} : Set TernaryRing) := by
  obtain ⟨q, hq⟩ := esymmAlgHom_surjective (σ := Fin 3) ℤ (n := 3) le_rfl
    ⟨p, (mem_symmetricSubalgebra p).mpr hp⟩
  have hpq : p = aeval (fun i : Fin 3 => esymm (Fin 3) ℤ (i + 1)) q := by
    rw [← esymmAlgHom_apply, hq]
  have hle : (aeval (fun i : Fin 3 => esymm (Fin 3) ℤ (i + 1))).range ≤
      Algebra.adjoin ℤ ({e 1, e 2, e 3, delta} : Set TernaryRing) := by
    rw [← Algebra.adjoin_range_eq_range_aeval]
    apply Algebra.adjoin_le
    rintro _ ⟨i, rfl⟩
    apply Algebra.subset_adjoin
    fin_cases i <;> simp
  exact hle ⟨q, hpq.symm⟩

theorem «eqn:C3invariants» : CubicTargets.ToricHeights.C3Invariants.Claim := by
  apply le_antisymm
  · intro f hf
    have hf' : rename (finRotate 3) f = f := (AlgHom.mem_equalizer _ _ _).mp hf
    obtain ⟨S, B, hS, hB, rfl⟩ := exists_symmetric_decomposition f hf'
    exact Subalgebra.add_mem _ (symmetric_mem_adjoin hS)
      (Subalgebra.mul_mem _ (symmetric_mem_adjoin hB)
        (Algebra.subset_adjoin (by simp)))
  · apply Algebra.adjoin_le
    intro p hp
    rw [SetLike.mem_coe, invariants, AlgHom.mem_equalizer]
    change rename (finRotate 3) p = p
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact esymm_isSymmetric (Fin 3) ℤ 1 (finRotate 3)
    · exact esymm_isSymmetric (Fin 3) ℤ 2 (finRotate 3)
    · exact esymm_isSymmetric (Fin 3) ℤ 3 (finRotate 3)
    · exact rename_cycle_delta

end Cubic.ToricHeights.C3Invariants
