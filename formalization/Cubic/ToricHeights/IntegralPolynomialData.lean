import Cubic.ToricHeights.AffineInvariantRing
import Cubic.PoissonSummation.AdelicHeightZetaData
import Cubic.Counting.PolynomialCountData

/-!
# Polynomial and height data on the original integral quotient points

Integrality tests every function in the original affine invariant ring. The
two coefficients are the descended symmetric functions, and the height is
the original adelic height: the toric height is defined as the real part of the
adelic height, not by a coefficient formula. `IntegralPolynomialHeight.height_real`
shows that this height is real.
-/

noncomputable section

namespace Cubic.ToricHeights.IntegralPolynomialData

open Cubic.QuadraticCorrespondence.DescendedCoefficients
open Cubic.PoissonSummation

abbrev Points := {P : AdelicHeightZetaData.RationalPoints // AffineInvariantRing.IntegralPoint P}

def linear (P : Points) : ℤ := (P.val linearCoefficient).num

def constant (P : Points) : ℤ := (P.val constantCoefficient).num

def polynomial (P : Points) : Polynomial ℤ :=
  Cubic.Counting.PolynomialCountData.traceOneCubic (linear P) (constant P)

def rootHeight (P : Points) : ℝ := Cubic.Counting.PolynomialCountData.rootHeight (polynomial P)

def toricHeight (P : Points) : ℝ :=
  (AdelicHeightZetaData.height 1 0 (RationalAdelicEmbedding.diagonal P.val)).re

end Cubic.ToricHeights.IntegralPolynomialData
