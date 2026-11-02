import Cubic.BoxAsymptotic.AngularLocalSeries
import Cubic.BoxAsymptotic.AngularIdeals

/-! The exact local factor `eq:Fk`, for the original angular measure and the
actual ideal-character series `D_k`. Both series converge absolutely on `Re s > 1`.
The character has the paper's positive Fourier convention. Analytic continuation
through the product `eq:Dk` remains a separate obligation. -/

noncomputable section

namespace Cubic.BoxAsymptotic.AngularSeries

open CubicTargets.BoxAsymptotic

/-- The angular identity `eq:Fk`, including odd-mode cancellation and absolute
convergence. The zero-frequency majorant is proved convergent by the direct
fourfold divisor comparison. -/
theorem «eq:Fk» : AngularSeriesClaim := by
  obtain ⟨hsum, hodd, heven⟩ := AngularLocalSeries.local_series_claim
  refine ⟨hsum, hodd, fun k hk s hs => ?_⟩
  simpa only [AngularIdeals.series_eq, funext (AngularIdeals.coefficient_eq k)] using
    heven k hk s hs

end Cubic.BoxAsymptotic.AngularSeries
