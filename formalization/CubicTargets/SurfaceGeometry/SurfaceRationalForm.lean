import Cubic.SurfaceGeometry.RationalFormData
import Cubic.SurfaceGeometry.LocalizedCubicData
import CubicTargets.SurfaceGeometry.SurfaceIntegralCubic
import CubicTargets.SurfaceGeometry.SurfaceCoordinateChange

/-! The rational cubic in its actual homogeneous coordinates, vertex charts,
and character-divisor quotient. The integral cubic's
graded embedding and canonical twist certify that the anticanonical bundle
is the ample hyperplane bundle. -/

namespace CubicTargets.SurfaceGeometry.SurfaceRationalForm

open Cubic.SurfaceGeometry RationalFormData CubicData
open Cubic.QuadraticCorrespondence.CyclotomicField

structure Claim : Prop where
  localized_coordinate_ring : ∃ e : LocalizedCubicData.NormCubicRing ≃ₐ[LocalizedCubicData.Base]
      LocalizedCubicData.OriginalCubicRing,
    ∀ p, e (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (LocalizedCubicData.normToOriginal p)
  localized_graded_coordinates : ∀ (p : LocalizedCubicData.Ambient) n, p.IsHomogeneous n →
    (LocalizedCubicData.normToOriginal p).IsHomogeneous n ∧
      (LocalizedCubicData.originalToNorm p).IsHomogeneous n
  coordinate_change : SurfaceCoordinateChange.Claim
  coordinate_ring : ∃ e : NormCubicRing ≃ₐ[ℚ] RationalCubicRing,
    ∀ p, e (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (normToOriginal p)
  graded_coordinates : ∀ (p : Ambient) n, p.IsHomogeneous n →
    (normToOriginal p).IsHomogeneous n ∧ (originalToNorm p).IsHomogeneous n
  anticanonical_embedding : SurfaceIntegralCubic.Claim
  geometric_picard_rank : Module.finrank ℚ Picard = 1
  simplicial_fan : ∀ i : Fin 3, ResolutionData.det (originalRay i) (originalRay (i+1)) = 3
  complete_fan : ∀ v : ℝ × ℝ, ∃ i : Fin 3,
    0 ≤ ResolutionData.detReal ((originalRay i).1,(originalRay i).2) v ∧
    0 ≤ ResolutionData.detReal v ((originalRay (i+1)).1,(originalRay (i+1)).2)
  split_equation : ∀ (k : Type) [Field k] [CharZero k] (r : k), r ^ 2 = -3 →
    ∀ x, splitCubic (splitChange r x) = normCubic x
  split_inverse : ∀ (k : Type) [Field k] [CharZero k] (r : k), r ≠ 0 →
    (∀ x, inverseSplitChange r (splitChange r x) = x) ∧
      (∀ x, splitChange r (inverseSplitChange r x) = x)
  split_singularities : ∀ (k : Type) [Field k] [CharZero k] (x : Fin 4 → k),
    SplitSingular k x ↔ ∃ (i : Fin 3) (c : k), c ≠ 0 ∧ x = c • splitVertex i
  norm_singularities : ∀ (k : Type) [Field k] [CharZero k] (r : k), r ^ 2 = -3 →
    ∀ x, NormSingular k x ↔ ∃ (i : Fin 3) (c : k), c ≠ 0 ∧ x = c • normVertex r i
  rational_singularity : ∀ x : Fin 4 → ℚ,
    NormSingular ℚ x ↔ ∃ c : ℚ, c ≠ 0 ∧ x = c • splitVertex 0
  singularities_distinct : ∀ i j : Fin 3, ∀ c : E, c ≠ 0 →
    singularVector i = c • singularVector j → i = j
  conjugate_pair : (fun j => conjugation (singularVector 1 j)) = singularVector 2
  rational_fixed : (fun j => conjugation (singularVector 0 j)) = singularVector 0
  local_A2 : ∀ (k : Type) [Field k] (i : Fin 3),
    (∀ u : Fin 3 → k, splitCubic (vertexChart i u) = u 0 * u 1 - u 2 ^ 3) ∧
    (∀ u : Fin 3 → k, vertexCoordinates i (vertexChart i u) = u) ∧
    (∀ x : Fin 4 → k, x ⟨i.val, by omega⟩ = 1 → vertexChart i (vertexCoordinates i x) = x) ∧
    vertexChart (k := k) i 0 = splitVertex i
  boundary : ∀ v : Fin 4 → ℚ,
    (coordinateChange v 0 = 0 ∧ coordinateChange v 3 = 0) ↔ v 0 = 0 ∧ v 1 = 0

end CubicTargets.SurfaceGeometry.SurfaceRationalForm
