import Cubic.SurfaceGeometry.RationalFormData
import Cubic.SurfaceGeometry.LocalizedCubicData
import Mathlib.RingTheory.MvPolynomial.Homogeneous

namespace CubicTargets.SurfaceGeometry.SurfaceNormCubic

open Cubic.SurfaceGeometry.RationalFormData
open Cubic.SurfaceGeometry

structure Claim : Prop where
  localized_presentation : ∃ e : LocalizedCubicData.NormCubicRing ≃ₐ[LocalizedCubicData.Base]
      LocalizedCubicData.OriginalCubicRing,
    ∀ p, e (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (LocalizedCubicData.normToOriginal p)
  localized_homogeneous : ∀ (p : LocalizedCubicData.Ambient) n, p.IsHomogeneous n →
    (LocalizedCubicData.normToOriginal p).IsHomogeneous n ∧
      (LocalizedCubicData.originalToNorm p).IsHomogeneous n
  presentation : ∃ e : NormCubicRing ≃ₐ[ℚ] RationalCubicRing,
    ∀ p, e (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (normToOriginal p)
  homogeneous : ∀ (p : Ambient) n, p.IsHomogeneous n →
    (normToOriginal p).IsHomogeneous n ∧ (originalToNorm p).IsHomogeneous n

end CubicTargets.SurfaceGeometry.SurfaceNormCubic
