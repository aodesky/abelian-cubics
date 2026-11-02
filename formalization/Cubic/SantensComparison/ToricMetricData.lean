import Cubic.PoissonSummation.AdelicHeightZetaData
import Cubic.Counting.IntegralPointCountData

/-! Support-function heights and integral models for the quadratic torus.
These definitions allow a literature theorem to quantify over metrics and
integral models, without taking a cubic counting function or a proposed
leading coefficient as part of its data. Local place weights are the actual
residue cardinalities divided by the global degree. -/

noncomputable section

namespace Cubic.SantensComparison.ToricMetricData

open Cubic.ToricHeights Cubic.QuadraticCorrespondence
open Cubic.PoissonSummation QuotientFiniteFourierProduct QuotientLocalFourier
open CubicTargets.PoissonSummation.FiniteFourierProduct
open CyclotomicField CyclotomicTorusGalois QuotientFiniteHeight
open FiniteEulerProduct

local instance primeFact (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

abbrev Support := (ℝ × ℝ) → ℂ
abbrev IntegralModel := Subalgebra ℤ quotientFixedRing

def splitHeight (φ : Support) (p : ℕ) [Fact p.Prime] [Fact (p%3=1)]
    (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) : ℂ :=
  (Nat.card (IsLocalRing.ResidueField ℤ_[p]) : ℂ) ^
      (φ (splitCoordinates p P) / Module.finrank ℚ E) *
    (Nat.card (IsLocalRing.ResidueField ℤ_[p]) : ℂ) ^
      (φ (splitSecondCoordinates p P) / Module.finrank ℚ E)

def inertHeight (φ : Support) (p : ℕ) [Fact p.Prime] [Fact (p%3=2)]
    (P : quotientFixedRing →ₐ[ℚ] ℚ_[p]) : ℂ :=
  (Nat.card (IsLocalRing.ResidueField (CyclotomicInertField.integers p)) : ℂ) ^
    (φ (inertCoordinates p P) / Module.finrank ℚ E)

def ramifiedHeight (φ : Support) (P : quotientFixedRing →ₐ[ℚ] ℚ_[3]) : ℂ :=
  (Nat.card (IsLocalRing.ResidueField CyclotomicRamifiedField.integers) : ℂ) ^
    (φ (ramifiedCoordinates P) / Module.finrank ℚ E)

def finiteHeight (φ : Support) (p : Nat.Primes) : (family p).Carrier → ℂ := by
  by_cases hs : (p:ℕ)%3=1
  · letI : Fact ((p:ℕ)%3=1) := ⟨hs⟩
    rw [family_split ⟨p,hs⟩]
    exact splitHeight φ p
  by_cases hi : (p:ℕ)%3=2
  · letI : Fact ((p:ℕ)%3=2) := ⟨hi⟩
    rw [family_inert ⟨p,hi⟩]
    exact inertHeight φ p
  · rw [show family p=ramifiedData by simp [family,hs,hi]]
    exact ramifiedHeight φ

def infiniteHeight (φ : Support) (P : ArchimedeanQuotientLogarithm.Points) : ℂ :=
  (Real.exp 2 : ℂ) ^
    (φ (ArchimedeanQuotientLogarithm.localCocharacter P) / Module.finrank ℚ E)

def height (φ : Support) (P : AdelicData.Points) : ℂ :=
  infiniteHeight φ P.1 * ∏' p : Nat.Primes, finiteHeight φ p (P.2 p)

def Integral (A : IntegralModel) (P : AdelicHeightZetaData.RationalPoints) : Prop :=
  ∀ f ∈ A, ∃ z : ℤ, P f=z

def boundedPoints (A : IntegralModel) (φ : Support) (B : ℝ) :
    Set AdelicHeightZetaData.RationalPoints :=
  {P | Integral A P ∧ (height φ (RationalAdelicEmbedding.diagonal P)).re ≤ B}

def count (A : IntegralModel) (φ : Support) (B : ℝ) : ℕ :=
  Nat.card (boundedPoints A φ B)

/-- The current paper's model is the image of its original integral
invariant ring, before any choice of generators or coefficient conditions. -/
def paperModel : IntegralModel := AffineInvariantRing.invariantRestriction.range

def paperSupport : Support := supportFunction (-1) 0

theorem paper_model (P : AdelicHeightZetaData.RationalPoints) :
    Integral paperModel P ↔ AffineInvariantRing.IntegralPoint P := by
  constructor
  · intro h f
    exact h _ ⟨f,rfl⟩
  · rintro h f ⟨g,rfl⟩
    exact h g

private theorem transport_height {D F : LocalData} (h : D=F) (f : F.Carrier → ℂ)
    (hf : ∀ x, f x=F.inverseHeight (-1) 0 x) :
    ∀ x, ((congrArg (fun D => D.Carrier → ℂ) h).mpr f) x=D.inverseHeight (-1) 0 x := by
  subst F
  exact hf

theorem paper_finite_height (p : Nat.Primes) (P : (family p).Carrier) :
    finiteHeight paperSupport p P=(family p).inverseHeight (-1) 0 P := by
  by_cases hs : (p:ℕ)%3=1
  · letI : Fact ((p:ℕ)%3=1) := ⟨hs⟩
    simp only [finiteHeight, dif_pos hs]
    exact transport_height (family_split ⟨p,hs⟩) (splitHeight paperSupport p) (fun _ => rfl) P
  by_cases hi : (p:ℕ)%3=2
  · letI : Fact ((p:ℕ)%3=2) := ⟨hi⟩
    simp only [finiteHeight, dif_neg hs, dif_pos hi]
    exact transport_height (family_inert ⟨p,hi⟩) (inertHeight paperSupport p) (fun _ => rfl) P
  · simp only [finiteHeight, dif_neg hs, dif_neg hi]
    exact transport_height (F := ramifiedData) (by simp [family,hs,hi]) (ramifiedHeight paperSupport)
      (fun _ => rfl) P

theorem paper_height (P : AdelicData.Points) :
    height paperSupport P=AdelicHeightZetaData.height 1 0 P := by
  unfold height AdelicHeightZetaData.height AdelicData.inverseHeight
    FiniteAdelicData.inverseHeight
  simp only [neg_zero]
  congr 1
  exact tprod_congr (fun p => paper_finite_height p _)

theorem paper_bounded_points (B : ℝ) :
    boundedPoints paperModel paperSupport B=Cubic.Counting.IntegralPointCountData.boundedPoints B := by
  ext P
  simp only [boundedPoints, Cubic.Counting.IntegralPointCountData.boundedPoints,
    Set.mem_setOf_eq, paper_model, paper_height]

theorem paper_count (B : ℝ) : count paperModel paperSupport B=
    Cubic.Counting.IntegralPointCountData.count B := by
  rw [count, paper_bounded_points]
  rfl

end Cubic.SantensComparison.ToricMetricData
