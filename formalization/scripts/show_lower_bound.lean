/-
Run from `formalization/` after `lake build Cubic.BoxHeight.LowerBound`:
  lake env lean scripts/show_lower_bound.lean
Prints the statement of `thm:lower`, its axioms, and every definition its statement uses.
-/
import Cubic.BoxHeight.LowerBound

open CubicTargets.BoxHeight

-- the theorem and everything it rests on
#check @Cubic.BoxHeight.LowerBound.«thm:lower»
#print axioms Cubic.BoxHeight.LowerBound.«thm:lower»
#print axioms Cubic.BoxHeight.XiaoCounterexample.not_xiaoUpperBound

-- the claim
#print LowerClaim
#print boxCount
#print boxSet
#print Cubic.Counting.GeneralMonicData.monicCubic
#print Cubic.QuadraticCorrespondence.CorrespondencePolynomials.HasCyclicCubicGaloisGroup
#print Cubic.Counting.AsymptoticConstantsData.originalLeading
#print Cubic.Counting.AsymptoticConstantsData.originalInertFactor
#print Cubic.Counting.AsymptoticConstantsData.originalSplitFactor
#print Cubic.PoissonSummation.FiniteEulerProduct.InertPrimes
#print Cubic.PoissonSummation.FiniteEulerProduct.SplitPrimes

-- the assumed input (Widmer 2016, Theorem 1.1)
#print WidmerBlackBox.BlackBox
#print WidmerBlackBox.B
#print WidmerBlackBox.D
