import Cubic.SantensComparison.ToricMetricGeometry
import Cubic.SantensComparison.AffineConeAlgebra

/-! General fan and divisor data for the quadratic torus. The orbit
representatives are auxiliary enumerations; their exactness is an explicit
law. Both Picard lattices are cokernels of actual character-divisor maps.
No counting estimate or proposed leading coefficient is part of this data. -/

noncomputable section

namespace Cubic.SantensComparison.ToricPairData

open ToricFanData ToricMetricData ToricMetricGeometry
open Cubic.QuadraticCorrespondence.CyclotomicField (E)
open Cubic.QuadraticCorrespondence.DescendedCoefficients (CoverRing)
open Cubic.SurfaceGeometry.ResolutionData (detReal)

structure Pair where
  fan : Fan
  conjugate : Fin fan.size → Fin fan.size
  boundary : Finset (Fin fan.size)
  realFace : Fin fan.size
  openSize : ℕ
  openRay : Fin openSize → Fin fan.size
  openConjugate : Fin openSize → Fin openSize
  orbitSize : ℕ
  orbitRay : Fin orbitSize → Fin fan.size

namespace Pair

def pairing (P : Pair) (m : ℤ × ℤ) (i : Fin P.fan.size) : ℤ :=
  m.1*(P.fan.ray i).1+m.2*(P.fan.ray i).2

def Retained (P : Pair) (i : Fin P.fan.size) : Prop :=
  i ∉ P.boundary ∨ i=P.realFace

def BoundaryFace (P : Pair) (A : Finset (Fin P.fan.size)) : Prop :=
  (∀ i ∈ A, i ∈ P.boundary) ∧
    ∃ j, ∀ i ∈ A, i=j ∨ i=P.fan.next j

def StableFace (P : Pair) (A : Finset (Fin P.fan.size)) : Prop :=
  P.BoundaryFace A ∧ ∀ i ∈ A, P.conjugate i ∈ A

def openPrincipal (P : Pair) : (ℤ × ℤ) →ₗ[ℤ] (Fin P.openSize → ℤ) where
  toFun m i := P.pairing m (P.openRay i)
  map_add' m n := by ext i; dsimp [pairing]; ring
  map_smul' a m := by ext i; dsimp [pairing]; ring

abbrev OpenPicard (P : Pair) := (Fin P.openSize → ℤ) ⧸ P.openPrincipal.range

def adelicPrincipal (P : Pair) : ℤ →ₗ[ℤ] (Fin P.orbitSize → ℤ) where
  toFun a i := P.pairing (a,a) (P.orbitRay i)
  map_add' a b := by ext i; dsimp [pairing]; ring
  map_smul' a b := by ext i; dsimp [pairing]; ring

abbrev AdelicPicard (P : Pair) := (Fin P.orbitSize → ℤ) ⧸ P.adelicPrincipal.range

def openCharacters (P : Pair) : AddSubmonoid (ℤ × ℤ) where
  carrier := {m | ∀ i, 0 ≤ P.pairing m (P.openRay i)}
  zero_mem' := by simp [pairing]
  add_mem' := by
    intro a b ha hb i
    have h₁ := ha i
    have h₂ := hb i
    dsimp [pairing] at *
    nlinarith

def coneAlgebra (P : Pair) : Subalgebra E CoverRing :=
  (AddMonoidAlgebra.mapDomainAlgHom E E P.openCharacters.subtype).range

def openSupport (P : Pair) : Set (ℝ × ℝ) :=
  ⋃ i : {i : Fin P.fan.size // i ∉ P.boundary ∧ P.fan.next i ∉ P.boundary}, P.fan.cone i

def affineCone (P : Pair) (u v : Fin P.fan.size) : Set (ℝ × ℝ) :=
  {x | 0 ≤ detReal (P.fan.realRay u) x ∧ 0 ≤ detReal x (P.fan.realRay v)}

/-- The laws of a smooth complete Galois fan, together with exact
enumerations of the open rays and the retained arithmetic orbit divisors. -/
structure Laws (P : Pair) : Prop where
  smooth_complete : P.fan.SmoothComplete
  conjugate_involutive : Function.Involutive P.conjugate
  conjugate_ray : ∀ i, P.fan.ray (P.conjugate i)=(P.fan.ray i).swap
  conjugate_next : ∀ i, P.fan.next (P.conjugate (P.fan.next i))=P.conjugate i
  boundary_stable : ∀ i, P.conjugate i ∈ P.boundary ↔ i ∈ P.boundary
  open_exact : ∀ i, i ∉ P.boundary ↔ ∃! j, P.openRay j=i
  open_conjugate : ∀ i, P.openRay (P.openConjugate i)=P.conjugate (P.openRay i)
  open_conjugate_involutive : Function.Involutive P.openConjugate
  orbit_retained : ∀ j, P.Retained (P.orbitRay j)
  orbit_exact : ∀ i, P.Retained i →
    ∃! j, i=P.orbitRay j ∨ i=P.conjugate (P.orbitRay j)
  face_boundary : P.realFace ∈ P.boundary
  face_ray : P.fan.ray P.realFace=(-1,-1)
  real_faces : ∀ A, P.StableFace A ↔ A=∅ ∨ A={P.realFace}

/-- Algebraic and metric hypotheses needed for the toric counting theorem.
The affine cone and ring conditions express the proper map to the chosen
integral model; the regular-character conditions express its unit and
analytic-obstruction hypotheses. -/
structure Applicability (P : Pair) (A : IntegralModel) (φ : Support) : Prop where
  fan_laws : P.Laws
  metric : CanonicalMetric P.fan φ
  finite_generation : A.FG
  generic_fibre : Algebra.adjoin E (AffineConeAlgebra.expansion ''
    (A : Set Cubic.QuadraticCorrespondence.CyclotomicTorusGalois.quotientFixedRing)) = P.coneAlgebra
  proper_support : ∃ u v, 0 < detReal (P.fan.realRay u) (P.fan.realRay v) ∧
    P.openSupport=P.affineCone u v
  pure_open : ∀ i, i ∉ P.boundary → ∃ j,
    j ∉ P.boundary ∧ P.fan.next j ∉ P.boundary ∧ (i=j ∨ i=P.fan.next j)
  constant_units : ∀ m, (∀ i, P.pairing m (P.openRay i)=0) → m=0
  no_obstruction : ∀ m ∈ P.openCharacters, 0 ≤ P.pairing m P.realFace → m=0

end Pair

end Cubic.SantensComparison.ToricPairData
