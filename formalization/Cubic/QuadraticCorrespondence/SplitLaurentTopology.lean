import Cubic.QuadraticCorrespondence.RegularFunctionTopology
import Cubic.QuadraticCorrespondence.SplitLaurentPoints
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Ring.Basic

/-!
# Topology of Laurent-coordinate points

Evaluation of each Laurent polynomial on pairs of units is continuous,
including negative powers. The coordinate-point bijection therefore respects
the topology defined by regular functions.
-/

noncomputable section

namespace Cubic.QuadraticCorrespondence.SplitLaurentTopology

open SplitLaurentInvariants SplitLaurentEvaluation SplitLaurentPoints
open scoped RegularFunctionTopology

variable {K R : Type*} [Field K] [CommRing R] [Algebra K R]
  [TopologicalSpace R] [IsTopologicalRing R]

theorem continuous_evaluate (b : LaurentRing (K := K)) :
    Continuous (fun x : Rˣ × Rˣ => evaluate x b) := by
  induction b using AddMonoidAlgebra.induction_on with
  | hM m =>
    change Continuous (fun x : Rˣ × Rˣ => evaluate x (AddMonoidAlgebra.single m 1))
    simp only [evaluate_single, map_one, one_mul]
    exact Units.continuous_val.comp ((continuous_fst.zpow m.1).mul (continuous_snd.zpow m.2))
  | hadd b c hb hc => simpa only [map_add] using hb.add hc
  | hsmul c b hb =>
    simp only [Algebra.smul_def, map_mul, AlgHom.commutes]
    exact continuous_const.mul hb

omit [IsTopologicalRing R] in
theorem continuous_coordinates :
    Continuous (coordinates (K := K) (R := R)) := by
  apply Continuous.prodMk
  · apply Units.continuous_iff.mpr
    exact ⟨RegularFunctionTopology.continuous_eval _, RegularFunctionTopology.continuous_eval _⟩
  · apply Units.continuous_iff.mpr
    exact ⟨RegularFunctionTopology.continuous_eval _, RegularFunctionTopology.continuous_eval _⟩

/-- Laurent points and pairs of units have the same topology: the evaluation
topology agrees with the unit-group topology. -/
def pointHomeomorph : (LaurentRing (K := K) →ₐ[K] R) ≃ₜ Rˣ × Rˣ where
  __ := pointEquiv
  continuous_toFun := continuous_coordinates
  continuous_invFun := (RegularFunctionTopology.continuous_iff _).mpr continuous_evaluate

end Cubic.QuadraticCorrespondence.SplitLaurentTopology
