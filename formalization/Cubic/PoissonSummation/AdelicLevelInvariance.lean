import Cubic.ToricHeights.QuotientCompactInvariance
import Cubic.PoissonSummation.AdelicCutoff
import Cubic.PoissonSummation.AdelicLevel

/-!
# Invariance of the actual cutoff height under `K^{D₀}`

The height is invariant under the full maximal compact. The integral cutoff
requires the exceptional congruence level at three. These pointwise identities
hold without any convergence assumption, before quotient integration.
-/

noncomputable section

namespace Cubic.PoissonSummation.AdelicLevel

open Cubic.QuadraticCorrespondence Cubic.ToricHeights
open AdelicCompactQuotient AdelicHeightZetaData QuotientCompactInvariance
open QuotientFiniteFourierProduct QuotientLocalFourier FiniteEulerProduct
open scoped RationalQuotientGroup RegularFunctionTopology QuotientLocalTopology
  AdelicHeightZetaData

theorem local_height_mul_compact (p : Nat.Primes) (s₀ σ : ℂ) :
    ∀ x k : (family p).Carrier, k ∈ (family p).maxCompact →
      (family p).inverseHeight s₀ σ (x * k) = (family p).inverseHeight s₀ σ x := by
  letI : Fact (p : ℕ).Prime := ⟨p.2⟩
  by_cases hs : (p : ℕ) % 3 = 1
  · letI : Fact ((p : ℕ) % 3 = 1) := ⟨hs⟩
    rw [family_split ⟨p, hs⟩]
    exact split_height_mul_compact p s₀ σ
  by_cases hi : (p : ℕ) % 3 = 2
  · letI : Fact ((p : ℕ) % 3 = 2) := ⟨hi⟩
    rw [family_inert ⟨p, hi⟩]
    exact inert_height_mul_compact p s₀ σ
  · have h : family p = ramifiedData := by simp [family, hs, hi]
    rw [h]
    exact ramified_height_mul_compact s₀ σ

theorem local_integral_mul_compact_iff (p : Nat.Primes) (hp : p ≠ primeThree) :
    ∀ x k : (family p).Carrier, k ∈ (family p).maxCompact →
      (x * k ∈ (family p).integralLocus ↔ x ∈ (family p).integralLocus) := by
  letI : Fact (p : ℕ).Prime := ⟨p.2⟩
  by_cases hs : (p : ℕ) % 3 = 1
  · letI : Fact ((p : ℕ) % 3 = 1) := ⟨hs⟩
    rw [family_split ⟨p, hs⟩]
    exact split_integral_mul_compact_iff p
  by_cases hi : (p : ℕ) % 3 = 2
  · letI : Fact ((p : ℕ) % 3 = 2) := ⟨hi⟩
    rw [family_inert ⟨p, hi⟩]
    exact inert_integral_mul_compact_iff p
  · have h0 : (p : ℕ) % 3 = 0 := by omega
    exact (hp (Subtype.ext
      ((p.property.dvd_iff_eq (by decide)).mp (Nat.dvd_of_mod_eq_zero h0)))).elim

theorem finite_height_mul_compact (s₀ σ : ℂ) (x k : FiniteAdelicData.Points)
    (hk : k ∈ finiteCompact) :
    FiniteAdelicData.inverseHeight s₀ σ (x * k) = FiniteAdelicData.inverseHeight s₀ σ x := by
  apply tprod_congr
  intro p
  exact local_height_mul_compact p s₀ σ (x p) (k p) (hk p)

theorem finite_integral_mul_level_iff (x k : FiniteAdelicData.Points)
    (hk : k ∈ finiteLevel) : x * k ∈ finiteIntegralLocus ↔ x ∈ finiteIntegralLocus := by
  change (∀ p, (x * k) p ∈ (family p).integralLocus) ↔ _
  apply forall_congr'
  intro p
  by_cases hp : p = primeThree
  · subst p
    change atThree (x * k) ∈ QuotientInvariantIntegrality.invariantLocus 3 ↔
      atThree x ∈ QuotientInvariantIntegrality.invariantLocus 3
    rw [← ramifiedLevel_carrier, map_mul]
    exact ramifiedLevel.mul_mem_cancel_right hk.2
  · exact local_integral_mul_compact_iff p hp (x p) (k p) (hk.1 p)

theorem height_mul_compact (s₀ σ : ℂ) (x k : AdelicData.Points)
    (hk : k ∈ maximalCompact) :
    AdelicData.inverseHeight s₀ σ (x * k) = AdelicData.inverseHeight s₀ σ x := by
  have hi : ArchimedeanQuotientLogarithm.coordinate k.1 = 0 := hk.1
  simp only [AdelicData.inverseHeight, Prod.fst_mul, Prod.snd_mul,
    ArchimedeanQuotientLogarithm.inverseHeight_eq,
    ArchimedeanQuotientLogarithm.coordinate_mul, hi, add_zero,
    finite_height_mul_compact s₀ σ x.2 k.2 hk.2]

theorem integral_mul_level_iff (x k : AdelicData.Points) (hk : k ∈ level) :
    x * k ∈ integralLocus ↔ x ∈ integralLocus :=
  finite_integral_mul_level_iff x.2 k.2 hk.2

/-- The exact invariance invoked in the second equality of the paper's unfolding. -/
theorem cutoffHeight_mul_level (s₀ σ : ℂ) (x k : AdelicData.Points) (hk : k ∈ level) :
    cutoffHeight s₀ σ (x * k) = cutoffHeight s₀ σ x := by
  classical
  by_cases hx : x ∈ integralLocus
  · rw [cutoffHeight, Set.indicator_of_mem ((integral_mul_level_iff x k hk).mpr hx),
      Set.indicator_of_mem hx]
    exact height_mul_compact s₀ σ x k (level_le_maximalCompact hk)
  · rw [cutoffHeight, Set.indicator_of_notMem
      (fun h => hx ((integral_mul_level_iff x k hk).mp h)), Set.indicator_of_notMem hx]

end Cubic.PoissonSummation.AdelicLevel
