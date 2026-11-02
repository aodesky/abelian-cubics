import Cubic.PoissonSummation.AdelicCompactQuotient
import Cubic.PoissonSummation.QuotientLocalMeasure

/-!
# The paper's compact congruence level

`K^{D₀}` has the second ramified congruence subgroup at three, maximal compacts
at the other finite places, and the angular compact at infinity. The congruence
subgroup is defined from the existing actual local integer ring and reduction.
-/

noncomputable section

namespace Cubic.PoissonSummation.AdelicLevel

open Cubic.QuadraticCorrespondence Cubic.ToricHeights
open CyclotomicTorusGalois AdelicCompactQuotient FiniteEulerProduct
open scoped RationalQuotientGroup RegularFunctionTopology QuotientLocalTopology

def localLevelModel : Subgroup RamifiedLocalModel.Points :=
  RamifiedLocalModel.congruenceSubgroup.map RamifiedLocalModel.compactUnits.subtype

theorem localLevelModel_carrier : (localLevelModel : Set RamifiedLocalModel.Points) =
    RamifiedLocalModel.integralLocus := rfl

def ramifiedLevel : Subgroup (quotientFixedRing →ₐ[ℚ] ℚ_[3]) :=
  localLevelModel.comap QuotientLocalModels.ramifiedEquiv.toMonoidHom

theorem ramifiedLevel_carrier : (ramifiedLevel : Set (quotientFixedRing →ₐ[ℚ] ℚ_[3])) =
    QuotientInvariantIntegrality.invariantLocus 3 :=
  QuotientLocalMeasure.ramified_preimage_integralLocus

def atThree : FiniteAdelicData.Points →* (quotientFixedRing →ₐ[ℚ] ℚ_[3]) where
  toFun x := x primeThree
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Finite components of the compact level in the original restricted product. -/
def finiteLevel : Subgroup FiniteAdelicData.Points :=
  finiteCompact ⊓ ramifiedLevel.comap atThree

/-- The full subgroup `K^{D₀}` in the paper. -/
def level : Subgroup AdelicData.Points := ArchimedeanHaar.coordinateHom.ker.prod finiteLevel

theorem finiteLevel_le_compact : finiteLevel ≤ finiteCompact := inf_le_left

theorem level_le_maximalCompact : level ≤ maximalCompact :=
  Subgroup.prod_mono le_rfl finiteLevel_le_compact

theorem atThree_finiteDiagonal (P : RationalAdelicEmbedding.Points) :
    atThree (RationalAdelicEmbedding.finiteDiagonal P) =
      RationalAdelicEmbedding.baseChange ℚ_[3] P := rfl

end Cubic.PoissonSummation.AdelicLevel
