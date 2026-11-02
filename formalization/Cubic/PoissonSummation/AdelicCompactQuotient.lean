import Cubic.PoissonSummation.ArchimedeanHaar
import Cubic.PoissonSummation.RestrictedProductHaar

/-!
# The concrete maps in the adelic logarithm sequence

These are the actual quotient by the rational diagonal, the product of the local
maximal compacts, its rational intersection, and the induced logarithm. The
assertion that its kernel is exhausted by this compact image is stated separately
in the target for `prop:Lmap` and proved in `LogarithmExactSequence`.
-/

noncomputable section

namespace Cubic.PoissonSummation.AdelicCompactQuotient

open Cubic.QuadraticCorrespondence Cubic.ToricHeights
open QuotientFiniteFourierProduct RationalAdelicEmbedding AdelicRationalCharacter
open scoped RationalQuotientGroup RegularFunctionTopology QuotientLocalTopology

/-- The coordinate `u` in `ell(x)=u v₀`, hence the minus sign. -/
def coordinate : AdelicData.Points →* Multiplicative ℝ where
  toFun x := Multiplicative.ofAdd (-(AdelicData.logarithm x).1)
  map_one' := by simp [AdelicData.logarithm_one]
  map_mul' x y := by
    change -(AdelicData.logarithm (x * y)).1 =
      -(AdelicData.logarithm x).1 + -(AdelicData.logarithm y).1
    rw [AdelicData.logarithm_mul, Prod.fst_add, neg_add]

theorem continuous_coordinate : Continuous coordinate :=
  AdelicData.continuous_logarithm.fst.neg

@[simp]
theorem coordinate_radialSection (u : ℝ) :
    coordinate (AdelicData.radialSection u) = Multiplicative.ofAdd u := by
  change -(AdelicData.logarithm (AdelicData.radialSection u)).1 = u
  simp [AdelicData.logarithm_radialSection]

theorem rational_le_ker : diagonal.range ≤ coordinate.ker := by
  rintro x ⟨P, rfl⟩
  change -(AdelicData.logarithm (diagonal P)).1 = 0
  simp [logarithm_diagonal]

/-- The quotient logarithm is obtained from the proved product formula. -/
def quotientCoordinate : AutomorphicQuotient →* Multiplicative ℝ :=
  QuotientGroup.lift diagonal.range coordinate rational_le_ker

@[simp]
theorem quotientCoordinate_mk (x : AdelicData.Points) :
    quotientCoordinate (QuotientGroup.mk x) = coordinate x := rfl

theorem continuous_quotientCoordinate : Continuous quotientCoordinate :=
  (QuotientGroup.isQuotientMap_mk diagonal.range).continuous_iff.mpr continuous_coordinate

def finiteCompact : Subgroup FiniteAdelicData.Points :=
  RestrictedProductHaar.compactSubgroup (fun p => (family p).Carrier)
    (fun p => (family p).maxCompact)

/-- The product of the angular subgroup and all finite local maximal compacts. -/
def maximalCompact : Subgroup AdelicData.Points :=
  ArchimedeanHaar.coordinateHom.ker.prod finiteCompact

/-- `μmax = T(ℚ) ∩ Kmax`, viewed as a subgroup of `Kmax`. -/
def rationalCompact : Subgroup maximalCompact := diagonal.range.comap maximalCompact.subtype

abbrev CompactQuotient := maximalCompact ⧸ rationalCompact

/-- Inclusion of the compact subgroup followed by the actual rational quotient. -/
def compactToQuotient : maximalCompact →* AutomorphicQuotient :=
  (QuotientGroup.mk' diagonal.range).comp maximalCompact.subtype

/-- The left-hand arrow in the paper's sequence. -/
def compactMap : CompactQuotient →* AutomorphicQuotient :=
  QuotientGroup.lift rationalCompact compactToQuotient (by
    intro x hx
    change QuotientGroup.mk (x : AdelicData.Points) = (1 : AutomorphicQuotient)
    exact (QuotientGroup.eq_one_iff _).mpr hx)

end Cubic.PoissonSummation.AdelicCompactQuotient
