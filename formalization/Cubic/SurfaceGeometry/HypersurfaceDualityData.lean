import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-! The two-term dual complex used in hypersurface adjunction. Its coefficient
module is the actual top exterior power of the ambient Kähler differentials.
The cohomology is the cokernel of precomposition with multiplication by the
defining equation. No formula for the canonical twist is built into it. -/

noncomputable section

namespace Cubic.SurfaceGeometry.HypersurfaceDualityData

open MvPolynomial

variable (k : Type*) [Field k]

abbrev Ambient := MvPolynomial (Fin 4) k
abbrev TopForms : Type _ := ⋀[Ambient k]^4 Ω[Ambient k⁄k]
abbrev DualTerm := Ambient k →ₗ[Ambient k] TopForms k

instance : AddCommGroup (TopForms k) := inferInstance
instance : AddCommGroup (DualTerm k) := inferInstance

private instance topIndexUnique : Unique (Set.powersetCard (Fin 4) 4) where
  default := ⟨Finset.univ, by simp⟩
  uniq s := Subtype.ext (Finset.eq_univ_of_card s.val (by simpa using s.property))

/-- The coefficient of dA∧dB∧dC∧dD in the ambient top form. -/
def volumeCoefficient : TopForms k ≃ₗ[Ambient k] Ambient k :=
  ((KaehlerDifferential.mvPolynomialBasis k (Fin 4)).exteriorPower 4).equivFun.trans
    (LinearEquiv.funUnique (Set.powersetCard (Fin 4) 4) (Ambient k) (Ambient k))

def dualCoefficient : DualTerm k ≃ₗ[Ambient k] Ambient k :=
  (LinearMap.ringLmapEquivSelf (Ambient k) (Ambient k) (TopForms k)).trans
    (volumeCoefficient k)

def multiplication (f : Ambient k) : Ambient k →ₗ[Ambient k] Ambient k :=
  LinearMap.mulLeft (Ambient k) f

def dualDifferential (f : Ambient k) : DualTerm k →ₗ[Ambient k] DualTerm k where
  toFun φ := φ.comp (multiplication k f)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

abbrev DualCohomology (f : Ambient k) :=
  DualTerm k ⧸ LinearMap.range (dualDifferential k f)

/-- Degree of a polynomial coefficient in the ordinary integer grading. -/
def Homogeneous (f : Ambient k) (n : ℤ) : Prop :=
  IsWeightedHomogeneous (fun _ : Fin 4 => (1 : ℤ)) f n

/-- A degree-n map from the free module generated in degree a to the ambient
top forms. The four differentials each have degree one. -/
def HomogeneousMap (a : ℤ) (φ : DualTerm k) (n : ℤ) : Prop :=
  ∀ (d : ℤ) (p : Ambient k), Homogeneous k p d →
    Homogeneous k (volumeCoefficient k (φ p)) (d + a + n - 4)

/-- The quotient grading on the first cohomology of the dual complex. -/
def CohomologyDegree (f : Ambient k) (a n : ℤ) (x : DualCohomology k f) : Prop :=
  ∃ φ : DualTerm k, HomogeneousMap k a φ n ∧
    (LinearMap.range (dualDifferential k f)).mkQ φ = x

end Cubic.SurfaceGeometry.HypersurfaceDualityData
