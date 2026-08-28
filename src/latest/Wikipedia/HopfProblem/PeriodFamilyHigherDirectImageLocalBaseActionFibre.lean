import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageLocalBaseActionFibreBasic
import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageLocalBaseActionFibreCohomologyBasic
import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageFibreNaturalityBasic
import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageFibreComparison
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenBaseActionActions

/-!
# Actual neighborhood fibre evaluation is linear over local base functions

The genuine local coefficient multipliers commute with the original
neighborhood-to-fibre map in every degree. The proof factors the actual
coefficient restriction through the pushed-forward open holomorphic
sheaf and applies cohomology naturality to literal sheaf squares. The
local function need not extend to the ambient base.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.LocalBaseAction

open HolomorphicSheafCohomology PeriodFamilyHolomorphicCohomology

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]

local notation "IT" => modelWithCornersSelf ℂ (V × ComplexPlane₂)

namespace Fibre

/-- The original cohomology-presheaf map of literal restriction to the full open preimage. -/
def openCoefficientCohomologyMap (P : HolomorphicPeriodMap V B) (U : Opens B) (q : ℕ) :
    neighborhoodCohomology P U q ⟶
      CategoryTheory.Sheaf.H'.{0} (openPushforwardSheaf P U) q (Zero.basePreimage P U) :=
  ((CategoryTheory.Sheaf.cohomologyPresheafFunctor
    (Opens.grothendieckTopology (TopCat.of P.TotalSpace)) q).map
      (openCoefficientPullback P U)).app (op (Zero.basePreimage P U))

variable [IsManifold (modelWithCornersSelf ℂ V) ω B]

/-- The genuine coefficient map intertwines the original local action with pushed multiplication. -/
theorem openCoefficientCohomologyMap_smul (P : HolomorphicPeriodMap V B) (U : Opens B)
    (q : ℕ) (g : Zero.BaseSection P U) (x : neighborhoodCohomology P U q) :
    letI : Module (Zero.BaseSection P U) (neighborhoodCohomology P U q) :=
      OpenBaseAction.neighborhoodCohomologyModule P U q
    openCoefficientCohomologyMap P U q (g • x) =
      (((CategoryTheory.Sheaf.cohomologyPresheafFunctor
        (Opens.grothendieckTopology (TopCat.of P.TotalSpace)) q).map
          (pushedMultiplyEnd P U g)).app (op (Zero.basePreimage P U)))
            (openCoefficientCohomologyMap P U q x) := by
  let := P.totalChartedSpace
  let : Module (Zero.BaseSection P U) (neighborhoodCohomology P U q) :=
    OpenBaseAction.neighborhoodCohomologyModule P U q
  have hs := OpenBaseAction.neighborhoodCohomologyModule_smul P U q g x
  have hc := coefficient_open_intertwining IT (Zero.basePreimage P U)
    (openCoefficientPullback P U) (OpenBaseAction.preimageMultiplyEnd P U g)
    (pushedMultiplyEnd P U g) (openRestrictionCoefficient_multiply P U g) q x
  exact (congrArg (openCoefficientCohomologyMap P U q) hs).trans hc

variable [T2Space B]

/-- Actual fibre evaluation of the holomorphic sheaf defined on the full open preimage. -/
def pushedFibreEvaluation (P : HolomorphicPeriodMap V B) (b : B) (q : ℕ)
    (U : Opens B) (hb : b ∈ U) :
    CategoryTheory.Sheaf.H'.{0} (openPushforwardSheaf P U) q (Zero.basePreimage P U) →+
      PeriodTorusHolomorphicCohomology.H (P.point b) q :=
  FibreNeighborhood.cohomologyEvaluation (FibreGeometry.fibreMap P b)
    (FibreGeometry.fibreMap_isClosedMap P b) (FibreGeometry.fibreMap_finite_fibres P b)
    (fibreCoefficientPullback P U ⟨b, hb⟩) (Zero.basePreimage P U)
    (FibreGeometry.fibreMap_mem_fullPreimage P b hb) q

/-- Factoring through the actual open holomorphic sheaf preserves original fibre evaluation. -/
theorem pushedFibreEvaluation_openCoefficient (P : HolomorphicPeriodMap V B) (b : B)
    (q : ℕ) (U : Opens B) (hb : b ∈ U) (x : neighborhoodCohomology P U q) :
    pushedFibreEvaluation P b q U hb (openCoefficientCohomologyMap P U q x) =
      neighborhoodFibreEvaluation P b q U hb x := by
  have hsq : openCoefficientPullback P U ≫ fibreCoefficientPullback P U ⟨b, hb⟩ =
      FibreGeometry.coefficientPullback P b ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat (FibreGeometry.fibreMap P b)).map
          (𝟙 (PeriodTorusHolomorphicCohomology.holomorphicSheaf (P.point b))) := by
    have hi := (TopCat.Sheaf.pushforward AddCommGrpCat
      (FibreGeometry.fibreMap P b)).map_id
        (PeriodTorusHolomorphicCohomology.holomorphicSheaf (P.point b))
    have he := congrArg (fun f => FibreGeometry.coefficientPullback P b ≫ f) hi
    exact (openCoefficientPullback_fibre P U ⟨b, hb⟩).trans
      (he.trans (Category.comp_id (FibreGeometry.coefficientPullback P b))).symm
  exact (FibreNeighborhood.cohomologyEvaluation_naturality
    (FibreGeometry.fibreMap P b) (FibreGeometry.coefficientPullback P b)
    (fibreCoefficientPullback P U ⟨b, hb⟩) (openCoefficientPullback P U)
    (𝟙 (PeriodTorusHolomorphicCohomology.holomorphicSheaf (P.point b))) hsq
    (FibreGeometry.fibreMap_isClosedMap P b) (FibreGeometry.fibreMap_finite_fibres P b)
    (Zero.basePreimage P U) (FibreGeometry.fibreMap_mem_fullPreimage P b hb) q x).trans
      (CategoryTheory.Sheaf.H.map_id_apply _)

/-- The original local multiplier is the literal base-point scalar after actual fibre evaluation. -/
theorem pushedFibreEvaluation_multiply (P : HolomorphicPeriodMap V B) (b : B)
    (q : ℕ) (U : Opens B) (hb : b ∈ U) (g : Zero.BaseSection P U)
    (x : CategoryTheory.Sheaf.H'.{0} (openPushforwardSheaf P U) q (Zero.basePreimage P U)) :
    pushedFibreEvaluation P b q U hb
        ((((CategoryTheory.Sheaf.cohomologyPresheafFunctor
          (Opens.grothendieckTopology (TopCat.of P.TotalSpace)) q).map
            (pushedMultiplyEnd P U g)).app (op (Zero.basePreimage P U))) x) =
      g ⟨b, hb⟩ • pushedFibreEvaluation P b q U hb x :=
  FibreNeighborhood.cohomologyEvaluation_naturality
    (FibreGeometry.fibreMap P b) (fibreCoefficientPullback P U ⟨b, hb⟩)
    (fibreCoefficientPullback P U ⟨b, hb⟩) (pushedMultiplyEnd P U g)
    (FibreGeometry.fibreScalarEnd P b (g ⟨b, hb⟩)) (pushedMultiplyEnd_fibre P U g ⟨b, hb⟩)
    (FibreGeometry.fibreMap_isClosedMap P b) (FibreGeometry.fibreMap_finite_fibres P b)
    (Zero.basePreimage P U) (FibreGeometry.fibreMap_mem_fullPreimage P b hb) q x

end Fibre

variable [IsManifold (modelWithCornersSelf ℂ V) ω B] [T2Space B]

/-- Every local holomorphic base function acts on original neighborhood-to-fibre
cohomology by its actual base-point value, in all cohomological degrees. -/
theorem neighborhoodFibreEvaluation_smul (P : HolomorphicPeriodMap V B) (b : B)
    (q : ℕ) (U : Opens B) (hb : b ∈ U) (g : Zero.BaseSection P U)
    (x : neighborhoodCohomology P U q) :
    letI : Module (Zero.BaseSection P U) (neighborhoodCohomology P U q) :=
      OpenBaseAction.neighborhoodCohomologyModule P U q
    neighborhoodFibreEvaluation P b q U hb (g • x) =
      g ⟨b, hb⟩ • neighborhoodFibreEvaluation P b q U hb x := by
  let : Module (Zero.BaseSection P U) (neighborhoodCohomology P U q) :=
    OpenBaseAction.neighborhoodCohomologyModule P U q
  exact (Fibre.pushedFibreEvaluation_openCoefficient P b q U hb (g • x)).symm.trans
    ((congrArg (Fibre.pushedFibreEvaluation P b q U hb)
      (Fibre.openCoefficientCohomologyMap_smul P U q g x)).trans
        ((Fibre.pushedFibreEvaluation_multiply P b q U hb g
          (Fibre.openCoefficientCohomologyMap P U q x)).trans
            (congrArg (fun y => g ⟨b, hb⟩ • y)
              (Fibre.pushedFibreEvaluation_openCoefficient P b q U hb x))))

end Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.LocalBaseAction
