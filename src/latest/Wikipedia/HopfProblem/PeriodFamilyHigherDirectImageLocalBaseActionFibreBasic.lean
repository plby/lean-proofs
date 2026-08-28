import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageFibreGeometry
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenBaseActionBasic
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyHolomorphicRestrictionSheaf

/-!
# Genuine local holomorphic coefficients for fibre evaluation

The holomorphic sheaf on a full base preimage is pushed forward along
its actual open inclusion. Literal restriction factors the original
total-space-to-fibre coefficient morphism through this sheaf. A base
function defined only on that neighborhood acts there by its actual
pullback multiplier, and its restriction to the fibre is its value at
the base point. No extension of the local function is used.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.LocalBaseAction.Fibre

open HolomorphicSheafCohomology PeriodFamilyHolomorphicCohomology

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]

local notation "IT" => modelWithCornersSelf ℂ (V × ComplexPlane₂)
local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂

/-- The actual inclusion of the original full base preimage. -/
def openInclusion (P : HolomorphicPeriodMap V B) (U : Opens B) :
    TopCat.of (Zero.basePreimage P U) ⟶ TopCat.of P.TotalSpace :=
  OpenRestriction.inclusion (X := TopCat.of P.TotalSpace) (Zero.basePreimage P U)

/-- The original open-submanifold holomorphic sheaf pushed into the total space. -/
def openPushforwardSheaf (P : HolomorphicPeriodMap V B) (U : Opens B) :
    TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of P.TotalSpace) :=
  (TopCat.Sheaf.pushforward AddCommGrpCat (openInclusion P U)).obj
    (OpenClasses.preimageHolomorphicSheaf P U)

/-- Literal restriction from the actual total space to its full open preimage. -/
def openCoefficientPullback (P : HolomorphicPeriodMap V B) (U : Opens B) :
    Zero.totalAdditiveSheaf P ⟶ openPushforwardSheaf P U := by
  letI := P.totalChartedSpace
  exact CuspNormalization.SheafOverBase.additivePullback IT IT
    (𝟙 (TopCat.of P.TotalSpace)) (openInclusion P U)
    ⟨Subtype.val, contMDiff_subtype_val⟩ (fun _ => rfl)

/-- The actual coefficient map after canonical restriction to the open submanifold. -/
def openRestrictionCoefficient (P : HolomorphicPeriodMap V B) (U : Opens B) :
    OpenClasses.preimageHolomorphicSheaf P U ⟶
      (OpenRestriction.restriction (Zero.basePreimage P U)).obj
        (openPushforwardSheaf P U) := by
  letI := P.totalChartedSpace
  exact (HolomorphicRestriction.sheafIso IT (Zero.basePreimage P U)).inv ≫
    (OpenRestriction.restriction (Zero.basePreimage P U)).map (openCoefficientPullback P U)

variable [IsManifold (modelWithCornersSelf ℂ V) ω B]

/-- Restriction from the original full open preimage to its actual compact fibre. -/
def fibreCoefficientPullback (P : HolomorphicPeriodMap V B) (U : Opens B) (b : U) :
    openPushforwardSheaf P U ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat (FibreGeometry.fibreMap P b)).obj
        (PeriodTorusHolomorphicCohomology.holomorphicSheaf (P.point b)) := by
  letI := P.totalChartedSpace
  exact CuspNormalization.SheafOverBase.additivePullback IT I₂
    (openInclusion P U) (FibreGeometry.fibreMap P b)
    ⟨Zero.fibreOn P U b, Zero.fibreOn_holomorphic P U b⟩ (fun _ => rfl)

/-- Factoring through the open preimage retains the original fibre coefficient map. -/
theorem openCoefficientPullback_fibre (P : HolomorphicPeriodMap V B) (U : Opens B) (b : U) :
    openCoefficientPullback P U ≫ fibreCoefficientPullback P U b =
      FibreGeometry.coefficientPullback P b := by
  let := P.totalChartedSpace
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext W
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  apply ContMDiffMap.ext
  intro t
  rfl

/-- Literal multiplication by a local base function on the actual pushed-forward sheaf. -/
def pushedMultiplyEnd (P : HolomorphicPeriodMap V B) (U : Opens B)
    (g : Zero.BaseSection P U) : openPushforwardSheaf P U ⟶ openPushforwardSheaf P U :=
  (TopCat.Sheaf.pushforward AddCommGrpCat (openInclusion P U)).map
    (OpenBaseAction.preimageMultiplyEnd P U g)

/-- The local multiplier restricts to the literal complex scalar on the original fibre. -/
theorem pushedMultiplyEnd_fibre (P : HolomorphicPeriodMap V B) (U : Opens B)
    (g : Zero.BaseSection P U) (b : U) :
    pushedMultiplyEnd P U g ≫ fibreCoefficientPullback P U b =
      fibreCoefficientPullback P U b ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat (FibreGeometry.fibreMap P b)).map
          (FibreGeometry.fibreScalarEnd P b (g b)) := by
  let := P.totalChartedSpace
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext W
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  apply ContMDiffMap.ext
  intro t
  rfl

/-- Canonical open restriction intertwines the two literal local coefficient multipliers. -/
theorem openRestrictionCoefficient_multiply (P : HolomorphicPeriodMap V B) (U : Opens B)
    (g : Zero.BaseSection P U) :
    OpenBaseAction.preimageMultiplyEnd P U g ≫ openRestrictionCoefficient P U =
      openRestrictionCoefficient P U ≫
        (OpenRestriction.restriction (Zero.basePreimage P U)).map (pushedMultiplyEnd P U g) := by
  let := P.totalChartedSpace
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext W
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  apply ContMDiffMap.ext
  intro t
  rfl

end Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.LocalBaseAction.Fibre
