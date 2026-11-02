import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Ring

/-! The two cubic equations and the original linear coordinate change.
These are polynomial constructions over the indicated coefficient ring. -/

namespace Cubic.SurfaceGeometry.CubicData

def F {R : Type*} [CommRing R] (A B C D : R) : R :=
  B ^ 3 + A * D ^ 2 - A * B * D + 3 * A * C * D + A ^ 2 * C -
    6 * A * B * C + 9 * A * C ^ 2

def normCubic {R : Type*} [CommRing R] (x : Fin 4 → R) : R :=
  x 0 * (x 1 ^ 2 + 3 * x 2 ^ 2) - x 3 ^ 3

def splitCubic {R : Type*} [CommRing R] (x : Fin 4 → R) : R :=
  x 0 * x 1 * x 2 - x 3 ^ 3

def affineRelation {R : Type*} [CommRing R] (a b d : R) : R :=
  d ^ 2 - (a + 3 * b) * d + a ^ 3 + 6 * a * b + 9 * b ^ 2 - b

def coordinateChange {R : Type*} [Field R] [CharZero R] (v : Fin 4 → R) : Fin 4 → R :=
  ![v 0, v 0 - (9 / 2) * v 1 + (27 / 2) * v 2,
    3 * v 3 - (3 / 2) * v 1 + (9 / 2) * v 2, v 0 - 3 * v 1]

def inverseCoordinateChange {R : Type*} [Field R] [CharZero R] (x : Fin 4 → R) : Fin 4 → R :=
  ![x 0, (x 0 - x 3) / 3, (2 * x 1 + x 0 - 3 * x 3) / 27,
    (3 * x 2 + x 0 - x 1) / 9]

end Cubic.SurfaceGeometry.CubicData
