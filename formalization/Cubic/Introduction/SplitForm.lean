import CubicTargets.Introduction.SplitForm
import Cubic.Introduction.SurfaceQuadraticTwist
import Cubic.SurfaceGeometry.SurfaceCoordinateChange

noncomputable section

namespace Cubic.Introduction.SplitForm

open Cubic.SurfaceGeometry RationalFormData CubicData
open Cubic.QuadraticCorrespondence.CyclotomicField

theorem «eqn:splitForm» : CubicTargets.Introduction.SplitForm.Claim :=
  ⟨SurfaceCoordinateChange.«eqn:surfaceCoordinateChange»,
    SurfaceQuadraticTwist.splitLinearEquiv sqrtNegThree sqrtNegThree_ne_zero,
    (fun _ => rfl), (fun _ => rfl),
    RationalFormSplitting.splitting_equation sqrtNegThree sqrtNegThree_sq⟩

end Cubic.Introduction.SplitForm
