import Cubic.SurfaceGeometry.ResolutionData

/-! The resolution proposition in the canonical fan and divisor-lattice model.
Smoothness, minimality and crepancy are certified by the primitive subdivision;
projectivity by a strictly positive support divisor. Nefness uses the invariant
curve cone and bigness uses the actual divisor polytope. -/

namespace CubicTargets.SurfaceGeometry.SurfaceResolvedBoundary

open Cubic.SurfaceGeometry.ResolutionData

structure Claim : Prop where
  original_rays : ambientRay 0 = (-1,-1) ∧ ambientRay 3 = (1,0) ∧ ambientRay 6 = (0,1)
  complete : Complete
  smooth : ∀ i, det (rays i) (rays (next i)) = 1
  conjugate_rays : ∀ i, rays (-i) = ((rays i).2, (rays i).1)
  conjugate_cones : ∀ i, -(next i) = prev (-i)
  subdivision : ∀ i : Fin 9,
    (3 : ℤ) • rays i =
      (3 - (i.val % 3 : ℤ)) • rays ⟨3 * (i.val / 3), by omega⟩ +
        (i.val % 3 : ℤ) • rays ⟨(3 * (i.val / 3) + 3) % 9, Nat.mod_lt _ (by decide)⟩
  minimal : ∀ i : Fin 9, i.val % 3 ≠ 0 → det (rays (prev i)) (rays (next i)) = 2
  projective_support : ∀ i, 0 < curveIntersection ampleDivisor i
  crepant : ∀ i, (antiK i : ℝ) = -(Cubic.ToricHeights.supportFunction 1 1
    (((ambientRay i).1 : ℝ), ((ambientRay i).2 : ℝ))).re
  geometric_picard_rank : Module.finrank ℚ Picard = 7
  anticanonical_nef : Nef antiK
  anticanonical_big : Big antiK
  anticanonical_square : intersection antiK antiK = 3
  boundary_pullback : ∀ i, (pullbackThreeD0 i : ℝ) =
    -(Cubic.ToricHeights.supportFunction 3 0
      (((ambientRay i).1 : ℝ), ((ambientRay i).2 : ℝ))).re
  boundary_support : ∀ i, boundary i = if 0 < pullbackThreeD0 i then 1 else 0
  boundary_chain :
    (fun j : Fin 5 => selfIntersection (![7,8,0,1,2] j)) = ![-2,-2,-1,-2,-2]
  boundary_chain_intersections : ∀ i j : Fin 5,
    intersectionMatrix (boundaryOrder i) (boundaryOrder j) =
      if i = j then selfIntersection (boundaryOrder i)
      else if i.val + 1 = j.val ∨ j.val + 1 = i.val then 1 else 0
  canonical_boundary : intersection canonical boundary = -1
  boundary_square : intersection boundary boundary = -1
  log_square : intersection logDivisor logDivisor = 0
  log_nef : Nef logDivisor
  log_nontrivial : ∃ i, curveIntersection logDivisor i ≠ 0
  log_not_big : ¬ Big logDivisor
  log_big_iff_positive_square : Big logDivisor ↔ 0 < intersection logDivisor logDivisor

end CubicTargets.SurfaceGeometry.SurfaceResolvedBoundary
