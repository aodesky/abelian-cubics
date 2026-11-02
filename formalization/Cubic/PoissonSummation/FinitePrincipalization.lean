import CubicTargets.PoissonSummation.LogarithmExactSequence

/-!
# Assembling global generators over finitely many primes

The restricted-product condition makes the prescribed nonzero valuations
finitely supported. Multiplying rational generators supported at each such
prime therefore realizes all of them simultaneously. The existence of these
prime generators is retained as an explicit arithmetic obligation.
-/

noncomputable section

namespace Cubic.PoissonSummation.FinitePrincipalization

open Cubic.QuadraticCorrespondence
open QuotientFiniteFourierProduct RationalAdelicEmbedding
open CubicTargets.PoissonSummation.LogarithmExactSequence
open scoped RationalQuotientGroup

theorem of_primePrincipalization (h : PrimePrincipalization) : FinitePrincipalization := by
  classical
  intro x
  choose P hP hother using fun p => h p (x p)
  let S := x.property.toFinset
  refine ⟨∏ p ∈ S, P p, ?_⟩
  intro p
  let π := QuotientGroup.mk' (family p).maxCompact
  have hsame : π (localPoint p (P p)) = π (x p) := QuotientGroup.eq.mpr (hP p)
  have hoff (q : Nat.Primes) (hq : q ≠ p) : π (localPoint p (P q)) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (hother q p hq.symm)
  have hprod : π (localPoint p (∏ q ∈ S, P q)) = π (x p) := by
    rw [map_prod, map_prod]
    by_cases hp : p ∈ S
    · rw [Finset.prod_eq_single p]
      · exact hsame
      · intro q _ hq
        exact hoff q hq
      · exact fun hn => (hn hp).elim
    · have hx : x p ∈ (family p).maxCompact := by
        simpa only [S, Set.Finite.mem_toFinset, Set.mem_compl_iff, Set.mem_setOf_eq,
          not_not] using hp
      have hx' : π (x p) = 1 := (QuotientGroup.eq_one_iff _).mpr hx
      rw [hx']
      apply Finset.prod_eq_one
      intro q hq
      exact hoff q (fun he => hp (he ▸ hq))
  exact QuotientGroup.eq.mp hprod

end Cubic.PoissonSummation.FinitePrincipalization
