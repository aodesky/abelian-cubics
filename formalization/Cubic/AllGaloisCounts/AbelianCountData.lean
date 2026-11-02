import Cubic.AllGaloisCounts.CountData

noncomputable section

namespace Cubic.AllGaloisCounts.AbelianCountData

open CountData Polynomial

/-- Commutativity of the actual splitting-field Galois group. -/
def HasAbelianSplittingField (f : ℚ[X]) : Prop :=
  ∀ σ τ : f.Gal, σ * τ = τ * σ

def abelianSet (H : ℝ) : Set ℤ[X] :=
  {f | f ∈ cubicBox H ∧ HasAbelianSplittingField (f.map (Int.castRingHom ℚ))}

def abelianCount (H : ℝ) : ℕ := Nat.card (abelianSet H)

end Cubic.AllGaloisCounts.AbelianCountData
