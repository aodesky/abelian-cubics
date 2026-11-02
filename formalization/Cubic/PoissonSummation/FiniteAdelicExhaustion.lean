import Cubic.PoissonSummation.FiniteAdelicStages
import Mathlib.Order.Filter.AtTopBot.Finset

/-!
# Exhaustion by finite-place stages containing three

The nonnegative integrals over these increasing open subgroups exhaust the
integral over the full finite adelic group. The same finite sets are cofinal
for the already proved product of local integrals.
-/

noncomputable section

namespace Cubic.PoissonSummation.FiniteAdelicStages

open MeasureTheory Set Filter
open QuotientFiniteFourierProduct FiniteEulerProduct AdelicHeightZetaData
open scoped RestrictedProductHaar AdelicHeightZetaData ENNReal

def stageSet (S : Finset Nat.Primes) : Set FiniteAdelicData.Points := range (inclusion S)

theorem isOpen_stageSet (S : Finset Nat.Primes) : IsOpen (stageSet S) :=
  (RestrictedProductHaar.isOpenEmbedding_inclusion _ _ S).isOpen_range

theorem stageSet_mono : Monotone stageSet := by
  intro S T hST y hy
  obtain ⟨x, rfl⟩ := hy
  refine ⟨⟨x, ?_⟩, rfl⟩
  intro p hp
  exact x.property (fun hpS => hp (hST hpS))

def exhaustionPrimes (n : ℕ) : Finset Nat.Primes :=
  insert primeThree
    ((Set.finite_Iic n).preimage Subtype.val_injective.injOn).toFinset

@[simp]
theorem mem_exhaustionPrimes (p : Nat.Primes) (n : ℕ) :
    p ∈ exhaustionPrimes n ↔ p = primeThree ∨ (p : ℕ) ≤ n := by
  classical
  simp [exhaustionPrimes]

theorem exhaustionPrimes_mono : Monotone exhaustionPrimes := by
  intro m n hmn p hp
  simp only [mem_exhaustionPrimes] at hp ⊢
  exact hp.imp_right (fun h => h.trans hmn)

theorem exhaustionPrimes_tendsto : Tendsto exhaustionPrimes atTop atTop :=
  tendsto_atTop_finset_of_monotone exhaustionPrimes_mono
    (fun p => ⟨p, (mem_exhaustionPrimes p p).mpr (Or.inr le_rfl)⟩)

theorem iUnion_stageSet : (⋃ n, stageSet (exhaustionPrimes n)) = univ := by
  classical
  ext x
  simp only [mem_iUnion, mem_univ, iff_true]
  have hfin : {p | x p ∉ (family p).maxCompact}.Finite := x.property
  obtain ⟨n, hn⟩ := (exhaustionPrimes_tendsto.eventually (eventually_ge_atTop hfin.toFinset)).exists
  refine ⟨n, ⟨⟨x, ?_⟩, rfl⟩⟩
  intro p hp
  by_contra h
  exact hp (hn (hfin.mem_toFinset.mpr h))

theorem lintegral_eq_iSup_stages (f : FiniteAdelicData.Points → ℝ≥0∞) :
    (∫⁻ x, f x ∂finiteMeasure) =
      ⨆ n, ∫⁻ x in stageSet (exhaustionPrimes n), f x ∂finiteMeasure := by
  have h := setLIntegral_iUnion_of_directed (μ := finiteMeasure) f
    (s := fun n => stageSet (exhaustionPrimes n))
    (stageSet_mono.comp exhaustionPrimes_mono).directed_le
  simpa only [iUnion_stageSet, Measure.restrict_univ] using h

end Cubic.PoissonSummation.FiniteAdelicStages
