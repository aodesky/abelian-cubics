import Cubic.PoissonSummation.AdelicHeightZetaData
import Cubic.Counting.IntegralPointCountData

/-! Support-function heights and integral models for the quadratic torus.
These definitions allow a literature theorem to quantify over metrics and
integral models, without taking a cubic counting function or a proposed
leading coefficient as part of its data. Local place weights are the actual
residue cardinalities divided by the global degree.

A height is given by a support function at the real place and a separate
support function at each prime. Santens's finite local norms take values in
`p^ℤ`; no single support function for the class of `D₀′` has this property
at both split primes and the ramified prime 3, so the finite metrics must be
allowed to differ from the archimedean one. -/

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
/-- Support functions of the local metrics at the primes. -/
abbrev FiniteSupport := Nat.Primes → Support

/-- The ramified prime, as an index of the finite support functions. -/
def three : Nat.Primes := ⟨3,Nat.prime_three⟩

/-- The same support function at every prime. -/
def uniform (φ : Support) : FiniteSupport := fun _ => φ

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

/-- The height with real-place support function `φ` and finite support
functions `ψ`. -/
def height (φ : Support) (ψ : FiniteSupport) (P : AdelicData.Points) : ℂ :=
  infiniteHeight φ P.1 * ∏' p : Nat.Primes, finiteHeight (ψ p) p (P.2 p)

def Integral (A : IntegralModel) (P : AdelicHeightZetaData.RationalPoints) : Prop :=
  ∀ f ∈ A, ∃ z : ℤ, P f=z

def boundedPoints (A : IntegralModel) (φ : Support) (ψ : FiniteSupport) (B : ℝ) :
    Set AdelicHeightZetaData.RationalPoints :=
  {P | Integral A P ∧ (height φ ψ (RationalAdelicEmbedding.diagonal P)).re ≤ B}

def count (A : IntegralModel) (φ : Support) (ψ : FiniteSupport) (B : ℝ) : ℕ :=
  Nat.card (boundedPoints A φ ψ B)

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

private theorem transport_const {D F : LocalData} (h : D=F) (f : F.Carrier → ℂ) (c : ℂ)
    (hf : ∀ x, f x=c) : ∀ x, ((congrArg (fun D => D.Carrier → ℂ) h).mpr f) x=c := by
  subst F
  exact hf

/-- The zero support function gives the trivial local metric at every prime. -/
theorem finiteHeight_zero (p : Nat.Primes) (P : (family p).Carrier) :
    finiteHeight 0 p P=1 := by
  by_cases hs : (p:ℕ)%3=1
  · letI : Fact ((p:ℕ)%3=1) := ⟨hs⟩
    simp only [finiteHeight, dif_pos hs]
    exact transport_const (family_split ⟨p,hs⟩) (splitHeight 0 p) 1
      (fun _ => by simp [splitHeight]) P
  by_cases hi : (p:ℕ)%3=2
  · letI : Fact ((p:ℕ)%3=2) := ⟨hi⟩
    simp only [finiteHeight, dif_neg hs, dif_pos hi]
    exact transport_const (family_inert ⟨p,hi⟩) (inertHeight 0 p) 1
      (fun _ => by simp [inertHeight]) P
  · simp only [finiteHeight, dif_neg hs, dif_neg hi]
    exact transport_const (F := ramifiedData) (by simp [family,hs,hi]) (ramifiedHeight 0) 1
      (fun _ => by simp [ramifiedHeight]) P

theorem paper_height (P : AdelicData.Points) :
    height paperSupport (uniform paperSupport) P=AdelicHeightZetaData.height 1 0 P := by
  unfold height AdelicHeightZetaData.height AdelicData.inverseHeight
    FiniteAdelicData.inverseHeight
  simp only [neg_zero]
  congr 1
  exact tprod_congr (fun p => paper_finite_height p _)

theorem paper_bounded_points (B : ℝ) :
    boundedPoints paperModel paperSupport (uniform paperSupport) B=Cubic.Counting.IntegralPointCountData.boundedPoints B := by
  ext P
  simp only [boundedPoints, Cubic.Counting.IntegralPointCountData.boundedPoints,
    Set.mem_setOf_eq, paper_model, paper_height]

theorem paper_count (B : ℝ) : count paperModel paperSupport (uniform paperSupport) B=
    Cubic.Counting.IntegralPointCountData.count B := by
  rw [count, paper_bounded_points]
  rfl

end Cubic.SantensComparison.ToricMetricData
