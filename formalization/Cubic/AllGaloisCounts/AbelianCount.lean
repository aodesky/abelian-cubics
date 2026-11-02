import CubicTargets.AllGaloisCounts.AbelianCount
import Cubic.AllGaloisCounts.RealHeightBounds

/-! The final abelian-count consequence of the all-Galois appendix:
sum the trivial, quadratic and cyclic families, retaining real heights. -/

noncomputable section

namespace Cubic.AllGaloisCounts.AbelianCount
open Polynomial CountData AbelianCountData CountingIdentities GaloisClassification
open Filter Asymptotics

theorem type_abelian_iff {f : ℚ[X]} {G : GaloisType} (hG : HasGaloisType G f) :
    HasAbelianSplittingField f ↔ G ≠ .symmetric := by
  cases G with
  | trivial =>
    obtain ⟨e⟩ := hG
    suffices HasAbelianSplittingField f from ⟨fun _ => by decide, fun _ => this⟩
    intro σ τ
    apply e.injective
    simp only [map_mul, mul_comm]
  | quadratic =>
    obtain ⟨e⟩ := hG
    suffices HasAbelianSplittingField f from ⟨fun _ => by decide, fun _ => this⟩
    intro σ τ
    apply e.injective
    simp only [map_mul, mul_comm]
  | cyclic =>
    obtain ⟨e⟩ := hG
    suffices HasAbelianSplittingField f from ⟨fun _ => by decide, fun _ => this⟩
    intro σ τ
    apply e.injective
    simp only [map_mul, mul_comm]
  | symmetric =>
    obtain ⟨e⟩ := hG
    simp only [ne_eq, not_true_eq_false, iff_false]
    intro h
    have hc := congrArg e
      (h (e.symm (Equiv.swap (0 : Fin 3) 1)) (e.symm (Equiv.swap (1 : Fin 3) 2)))
    simp only [map_mul, e.apply_symm_apply] at hc
    exact (by decide : Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2 ≠
      Equiv.swap (1 : Fin 3) 2 * Equiv.swap (0 : Fin 3) 1) hc

theorem finite (H : ℝ) : (abelianSet H).Finite :=
  (HeightBox.cubicBox_finite H).subset (fun _ h => h.1)

theorem count_eq (H : ℝ) :
    abelianCount H = N .trivial H + N .quadratic H + N .cyclic H := by
  classical
  have he : abelianSet H = ↑((box H).filter
      (fun f => HasAbelianSplittingField (f.map (Int.castRingHom ℚ)))) := by
    ext f
    simp [abelianSet, mem_box]
  rw [abelianCount, Nat.card_coe_set_eq, he, Set.ncard_coe_finset, Finset.card_filter,
    type_count, type_count, type_count, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro f hf
  obtain ⟨G, hG⟩ := exists_type (IntegerRootCounts.rational_degree_three ((mem_box H f).mp hf))
  have ht : ∀ J, HasGaloisType J (f.map (Int.castRingHom ℚ)) ↔ J = G :=
    fun J => ⟨fun hJ => type_unique hJ hG, fun h => h ▸ hG⟩
  rw [type_abelian_iff hG]
  cases G <;> simp [indicator, ht]

theorem «eqn:abelianGaloisCount»
    (hPoisson : CubicTargets.PoissonSummation.PoissonWithDualMeasure.BlackBox)
    (hCN : CubicTargets.Counting.ChandrasekharanNarasimhanMeanSquare.BlackBox) :
    CubicTargets.AllGaloisCounts.AbelianCount.Claim := by
  refine ⟨finite, fun ε hε => ?_⟩
  have hs := SplitCubicCount.«lemma:splitCubicCount».2.trans
    (RealHeightBounds.square_isBigO ε hε)
  have hq := RealHeightBounds.quadratic.trans (RealHeightBounds.square_isBigO ε hε)
  have hc := CyclicCount.estimate hPoisson hCN ε hε
  apply ((hs.add hq).add hc).congr_left
  intro H
  rw [count_eq]
  push_cast
  dsimp [splitLeading]
  ring

end Cubic.AllGaloisCounts.AbelianCount
