import CubicTargets.AllGaloisCounts.LinearFactorSliceMoments
import Cubic.AllGaloisCounts.SliceVolume

/-! The complete slice-moment lemma: symmetry, regularity on the closed
parameter interval, the volume and the endpoint contribution. -/

namespace Cubic.AllGaloisCounts.LinearFactorSliceMoments

theorem «lemma:linearFactorSliceMoments» :
    CubicTargets.AllGaloisCounts.LinearFactorSliceMoments.Claim :=
  ⟨LinearFactorSlice.g_even, SlicePrimitive.g_contDiffOn,
    SliceVolume.volume, SlicePrimitive.boundary⟩

end Cubic.AllGaloisCounts.LinearFactorSliceMoments
