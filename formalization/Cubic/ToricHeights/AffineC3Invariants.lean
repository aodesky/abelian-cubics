import Cubic.ToricHeights.C3Invariants
import Cubic.ToricHeights.ChartDehomogenization
import CubicTargets.ToricHeights.AffineC3Invariants

/-!
# `eqn:affineC3invariants`: `ℤ[X/ε, Y/ε]^{C₃} = ℤ[e₂, e₃, δ]`

The paper's route: this is the dehomogenized form of `eqn:C3invariants`. A chart invariant
`f` is the dehomogenization of a form `F` (`exists_homogeneous_lift`); the form
`rename c⁻¹ F - F` has vanishing dehomogenization, hence is zero
(`eq_zero_of_dehom_eq_zero`), so `F` is a `C₃`-invariant form. By `eqn:C3invariants`,
`F ∈ ℤ[e₁,e₂,e₃,X²Y+Y²Z+Z²X]`, and dehomogenizing (`e₁ ↦ 1`) gives `f ∈ ℤ[e₂,e₃,δ]`.
The reverse inclusion is the invariance of the three generators.
-/

noncomputable section

namespace Cubic.ToricHeights.AffineC3Invariants

open MvPolynomial AffineInvariantRing ChartDehomogenization
open TernaryCyclicInvariants (TernaryRing e)

theorem esymm_two : e 2 = X 0 * X 1 + X 0 * X 2 + X 1 * X 2 := by
  have h : Finset.powersetCard 2 (Finset.univ : Finset (Fin 3)) = {{0,1},{0,2},{1,2}} := by
    decide
  show esymm (Fin 3) ℤ 2 = _
  rw [esymm, h, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp
  ring

theorem esymm_three : e 3 = X 0 * X 1 * X 2 := by
  have h : Finset.powersetCard 3 (Finset.univ : Finset (Fin 3)) = {{0,1,2}} := by decide
  simp [esymm, h]
  ring

theorem esymm_one : e 1 = X 0 + X 1 + X 2 := by
  simp [Fin.sum_univ_three]

/-- Dehomogenization carries `ℤ[e₁,e₂,e₃,X²Y+Y²Z+Z²X]` into `ℤ[e₂,e₃,δ]`. -/
theorem dehom_adjoin_le :
    Algebra.adjoin ℤ ({e 1, e 2, e 3, TernaryCyclicInvariants.delta} : Set TernaryRing) ≤
      (Algebra.adjoin ℤ ({AffineChartInvariants.e2, AffineChartInvariants.e3,
        AffineChartInvariants.delta} : Set ChartRing)).comap dehom := by
  apply Algebra.adjoin_le
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rw [SetLike.mem_coe, Subalgebra.mem_comap]
  rcases hp with rfl | rfl | rfl | rfl
  · have : dehom (e 1) = 1 := by
      rw [esymm_one]; simp [thirdCoordinate]
    rw [this]; exact Subalgebra.one_mem _
  · have : dehom (e 2) = AffineChartInvariants.e2 := by
      rw [esymm_two]; simp [linearPolynomial]; ring
    rw [this]; exact Algebra.subset_adjoin (by simp)
  · have : dehom (e 3) = AffineChartInvariants.e3 := by
      rw [esymm_three]; simp [AffineChartInvariants.e3]
    rw [this]; exact Algebra.subset_adjoin (by simp)
  · have : dehom TernaryCyclicInvariants.delta = AffineChartInvariants.delta := by
      simp [TernaryCyclicInvariants.delta, AffineChartInvariants.delta]
    rw [this]; exact Algebra.subset_adjoin (by simp)

theorem «eqn:affineC3invariants» : CubicTargets.ToricHeights.AffineC3Invariants.Claim := by
  apply le_antisymm
  · intro f hf
    have hf' : cycle f = f := (AlgHom.mem_equalizer _ _ _).mp hf
    obtain ⟨n, F, hF, rfl⟩ := exists_homogeneous_lift f
    have hinv : rename (finRotate 3).symm F = F := by
      apply sub_eq_zero.mp
      apply eq_zero_of_dehom_eq_zero (hF.rename_isHomogeneous.sub hF)
      rw [map_sub, dehom_rename_symm, hf', sub_self]
    have hinv' : rename (finRotate 3) F = F := by
      conv_lhs => rw [← hinv]
      rw [rename_rename]
      have : (finRotate 3 : Fin 3 → Fin 3) ∘ (finRotate 3).symm = id := by decide
      rw [this, rename_id_apply]
    have hmem : F ∈ TernaryCyclicInvariants.invariants := (AlgHom.mem_equalizer _ _ _).mpr hinv'
    rw [C3Invariants.«eqn:C3invariants»] at hmem
    exact dehom_adjoin_le hmem
  · apply Algebra.adjoin_le
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact AffineChartInvariants.e2_mem
    · exact AffineChartInvariants.e3_mem
    · exact AffineChartInvariants.delta_mem

end Cubic.ToricHeights.AffineC3Invariants
