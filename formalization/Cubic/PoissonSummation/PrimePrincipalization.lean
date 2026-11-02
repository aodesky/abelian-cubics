import Cubic.PoissonSummation.RationalPrimeCorrections
import Cubic.PoissonSummation.FinitePrincipalization

/-!
# Principalization of the actual finite adelic valuations

The split, inert and ramified corrections use global principal generators
and preserve compactness at all other primes. Their finite product proves the
arithmetic input needed for the paper's quotient and unfolding.
-/

noncomputable section

namespace Cubic.PoissonSummation.PrimePrincipalization

open Cubic.QuadraticCorrespondence Cubic.ToricHeights
open RationalAdelicEmbedding RationalPrimeGenerators RationalPrimeCorrections
open QuotientFiniteFourierProduct QuotientLocalFourier FiniteEulerProduct
open CubicTargets.PoissonSummation.FiniteFourierProduct (LocalData)
open scoped RationalQuotientGroup

private theorem transport_property {A : Type*} [Mul A]
    (Q : (D : LocalData) → (D.Carrier ≃* A) → Prop)
    {D F : LocalData} (h : D = F) (e : F.Carrier ≃* A) (he : Q F e) :
    Q D ((congrArg (fun D => D.Carrier ≃* A) h).mpr e) := by
  subst F
  exact he

theorem local_correction (p : Nat.Primes) (x : (family p).Carrier) :
    ∃ P : Points, P ∈ supportedAt p ∧ (localPoint p P)⁻¹ * x ∈ (family p).maxCompact := by
  letI : Fact (p : ℕ).Prime := ⟨p.2⟩
  suffices hh : ∀ x : (family p).Carrier, ∃ P : Points, P ∈ supportedAt p ∧
      ((originalEquiv p).symm (baseChange ℚ_[p] P))⁻¹ * x ∈ (family p).maxCompact from hh x
  let Q := fun (D : LocalData) (e : D.Carrier ≃* (CyclotomicTorusGalois.quotientFixedRing →ₐ[ℚ] ℚ_[p])) =>
    ∀ x : D.Carrier, ∃ P : Points, P ∈ supportedAt p ∧
      (e.symm (baseChange ℚ_[p] P))⁻¹ * x ∈ D.maxCompact
  change Q (family p) (originalEquiv p)
  by_cases hs : (p : ℕ) % 3 = 1
  · letI : Fact ((p : ℕ) % 3 = 1) := ⟨hs⟩
    simp only [originalEquiv, dif_pos hs]
    exact transport_property Q (family_split ⟨p, hs⟩) (MulEquiv.refl _) (split_correction p)
  by_cases hi : (p : ℕ) % 3 = 2
  · letI : Fact ((p : ℕ) % 3 = 2) := ⟨hi⟩
    simp only [originalEquiv, dif_neg hs, dif_pos hi]
    exact transport_property Q (family_inert ⟨p, hi⟩) (MulEquiv.refl _) (inert_correction p)
  · have h0 : (p : ℕ) % 3 = 0 := by omega
    have hp : p = primeThree := Subtype.ext
      ((p.property.dvd_iff_eq (by decide)).mp (Nat.dvd_of_mod_eq_zero h0))
    subst p
    exact ramified_correction

/-- Every prescribed local valuation has a rational representative supported at that prime. -/
theorem primePrincipalization : CubicTargets.PoissonSummation.LogarithmExactSequence.PrimePrincipalization := by
  intro p x
  obtain ⟨P, hP, hx⟩ := local_correction p x
  refine ⟨P, hx, ?_⟩
  intro q hq
  exact hP q (fun he => hq (Subtype.ext he))

/-- The unconditional class-number-one assertion on the original finite adelic torus. -/
theorem finitePrincipalization : CubicTargets.PoissonSummation.LogarithmExactSequence.FinitePrincipalization :=
  FinitePrincipalization.of_primePrincipalization primePrincipalization

end Cubic.PoissonSummation.PrimePrincipalization
