import Cubic.SurfaceGeometry.InvariantCubicData

noncomputable section

namespace Cubic.SurfaceGeometry.IntegralInvariantNormalForm

open MvPolynomial InvariantCubicData Cubic.ToricHeights.TernaryCyclicInvariants
open Cubic.ToricHeights.CyclicSymmetricDecomposition

theorem symmetricEval_symmetric (p : SymmetricCoefficients) :
    (symmetricEval p).IsSymmetric := by
  have h := (mem_symmetricSubalgebra _).mp (esymmAlgHom (Fin 3) ℤ 3 p).property
  simpa only [esymmAlgHom_apply, symmetricEval] using h

theorem symmetricEval_injective : Function.Injective symmetricEval := by
  intro p q h
  apply esymmAlgHom_injective ℤ (show 3 ≤ Fintype.card (Fin 3) by decide)
  apply Subtype.ext
  simpa only [esymmAlgHom_apply, symmetricEval] using h

theorem normalForm_injective : Function.Injective normalForm := by
  intro p q h
  have hτ := congrArg (rename swap01) h
  simp only [normalForm, map_add, map_mul,
    symmetricEval_symmetric p.1 swap01, symmetricEval_symmetric p.2 swap01,
    symmetricEval_symmetric q.1 swap01, symmetricEval_symmetric q.2 swap01] at hτ
  have hb : (symmetricEval p.2 - symmetricEval q.2) *
      (delta - rename swap01 delta) = 0 := by
    dsimp [normalForm] at h
    linear_combination h - hτ
  rw [delta_sub_swap, mul_neg, neg_eq_zero, mul_eq_zero] at hb
  have hB : symmetricEval p.2 = symmetricEval q.2 :=
    sub_eq_zero.mp (hb.resolve_right vandermonde_ne_zero)
  have hA : symmetricEval p.1 = symmetricEval q.1 := by
    dsimp [normalForm] at h
    rw [hB] at h
    exact add_right_cancel h
  exact Prod.ext (symmetricEval_injective hA) (symmetricEval_injective hB)

theorem exists_unique_normalForm (f : TernaryRing) (hf : f ∈ invariants) :
    ∃! p : SymmetricCoefficients × SymmetricCoefficients, normalForm p = f := by
  have hc : rename (finRotate 3) f = f := (AlgHom.mem_equalizer _ _ _).mp hf
  obtain ⟨S,B,hS,hB,he⟩ := exists_symmetric_decomposition f hc
  obtain ⟨p,hp⟩ := esymmAlgHom_surjective (σ := Fin 3) ℤ (n := 3) le_rfl ⟨S,hS⟩
  obtain ⟨q,hq⟩ := esymmAlgHom_surjective (σ := Fin 3) ℤ (n := 3) le_rfl ⟨B,hB⟩
  have hp' : symmetricEval p = S := by
    simpa only [esymmAlgHom_apply, symmetricEval] using congrArg Subtype.val hp
  have hq' : symmetricEval q = B := by
    simpa only [esymmAlgHom_apply, symmetricEval] using congrArg Subtype.val hq
  have hh : normalForm (p,q) = f := by simpa [normalForm, hp', hq'] using he.symm
  exact ⟨(p,q), hh, fun r hr => normalForm_injective (hr.trans hh.symm)⟩

end Cubic.SurfaceGeometry.IntegralInvariantNormalForm
