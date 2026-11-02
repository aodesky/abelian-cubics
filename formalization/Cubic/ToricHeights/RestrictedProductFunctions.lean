import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Sums and products of compact-trivial local functions

The finite adelic height and logarithm are assembled from local functions that
equal one or zero on the distinguished compact subgroups. For each restricted
product point only finitely many terms contribute. Continuity follows by
restricting to each finite-level piece of mathlib's restricted product.
-/

noncomputable section

namespace Cubic.ToricHeights.RestrictedProductFunctions

open Filter Function
open scoped RestrictedProduct

variable {ι : Type*} {R : ι → Type*} {A : (i : ι) → Set (R i)}
variable {M : Type*} [CommMonoid M]
variable (f : (i : ι) → R i → M) (hf : ∀ i x, x ∈ A i → f i x = 1)

include hf

@[to_additive]
theorem finite_mulSupport (x : Πʳ i, [R i, A i]) :
    (mulSupport (fun i => f i (x i))).Finite := by
  have h : ∀ᶠ i in cofinite, f i (x i) = 1 :=
    x.eventually.mono fun i hi => hf i (x i) hi
  exact h

variable [TopologicalSpace M]

@[to_additive]
theorem multipliable (x : Πʳ i, [R i, A i]) : Multipliable (fun i => f i (x i)) :=
  multipliable_of_finite_mulSupport (finite_mulSupport f hf x)

/-- Any finite set containing the exceptional places computes the entire product. -/
@[to_additive
  /-- Any finite set containing the exceptional places computes the entire sum. -/]
theorem prod_eq_prod (x : Πʳ i, [R i, A i]) (S : Finset ι)
    (hS : ∀ i ∉ S, x i ∈ A i) :
    ∏' i, f i (x i) = ∏ i ∈ S, f i (x i) :=
  tprod_eq_prod fun i hi => hf i (x i) (hS i hi)

@[to_additive]
theorem continuous_tprod [∀ i, TopologicalSpace (R i)] [ContinuousMul M]
    (hcont : ∀ i, Continuous (f i)) :
    Continuous (fun x : Πʳ i, [R i, A i] => ∏' i, f i (x i)) := by
  classical
  rw [RestrictedProduct.continuous_dom]
  intro S hS
  have hfin : Sᶜ.Finite := Filter.mem_cofinite.mp (Filter.le_principal_iff.mp hS)
  change Continuous (fun x : Πʳ i, [R i, A i]_[𝓟 S] => ∏' i, f i (x i))
  have heq : (fun x : Πʳ i, [R i, A i]_[𝓟 S] => ∏' i, f i (x i)) =
      (fun x => ∏ i ∈ hfin.toFinset, f i (x i)) := by
    funext x
    apply tprod_eq_prod
    intro i hi
    exact hf i (x i) (Filter.eventually_principal.mp x.eventually i (by simpa using hi))
  rw [heq]
  exact continuous_finset_prod _ fun i _ =>
    (hcont i).comp (RestrictedProduct.continuous_eval i)

omit hf in
/-- Including a single local component is continuous for the restricted-product topology. -/
theorem continuous_mulSingle {G : ι → Type*} [∀ i, Group (G i)]
    [∀ i, TopologicalSpace (G i)] [DecidableEq ι]
    (K : (i : ι) → Subgroup (G i)) (i : ι) :
    Continuous (RestrictedProduct.mulSingle K i) := by
  let hS : cofinite ≤ 𝓟 ({i}ᶜ : Set ι) := by simp
  let f : G i → Πʳ j, [G j, K j]_[𝓟 ({i}ᶜ : Set ι)] := fun x =>
    ⟨Pi.mulSingle i x, Filter.eventually_principal.mpr (by
      intro j hj
      have hji : j ≠ i := by simpa using hj
      rw [Pi.mulSingle_eq_of_ne hji]
      exact (K j).one_mem)⟩
  have hc : Continuous f := RestrictedProduct.continuous_rng_of_principal.mpr
    (_root_.continuous_mulSingle i)
  exact (RestrictedProduct.continuous_inclusion hS).comp hc

end Cubic.ToricHeights.RestrictedProductFunctions
