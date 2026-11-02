import Cubic.PoissonSummation.PoissonAdelicApplication
import CubicTargets.PoissonSummation.AdelicHeightZetaConvergence

/-!
# `lemma:heightZetaConvergence`: spatial and full-dual Fourier integrability

The proof follows the paper: finite-stage integrals and monotone convergence
give spatial integrability; counting-normalized unfolding and the coordinate
measure `du/6` give a summable base point; the support-function translation
bound gives absolute and locally uniform convergence everywhere, continuity,
and the original reciprocal-height series at zero. Support on the open level
annihilator and the actual coordinate Fourier majorant then give integrability
on the full automorphic dual, for every Haar normalization.

All data are the independently defined actual adelic torus, Haar measures,
rational points, cutoffs and heights. No Poisson hypothesis is used.
-/

namespace Cubic.PoissonSummation

theorem «lemma:heightZetaConvergence» :
    CubicTargets.PoissonSummation.AdelicHeightZetaConvergence.Claim where
  toPeriodization := adelicPeriodizationConvergence
  fourier_integrable := PoissonAdelicApplication.transform_integrable

end Cubic.PoissonSummation
