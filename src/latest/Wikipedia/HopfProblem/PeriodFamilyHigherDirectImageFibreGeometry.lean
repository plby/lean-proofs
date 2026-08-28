import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageFibreGeometryBasic
import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageZero
import Wikipedia.HopfProblem.CuspNormalizationSheafOverBase

/-!
# Actual holomorphic coefficient restriction to a native period-family fibre

The original holomorphic fibre inclusion pulls back actual sections on
every total-space open to sections on its literal fibre inverse image.
These maps give a genuine additive sheaf morphism to the pushforward
of the original fibre holomorphic sheaf. The original scalar maps and
all literal restrictions commute with this morphism. No cohomology or
base-change assertion is assumed or asserted here.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.FibreGeometry

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]

local notation "IB" => modelWithCornersSelf ℂ V
local notation "IT" => modelWithCornersSelf ℂ (V × ComplexPlane₂)
local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂

/-- Actual native holomorphic sections on an arbitrary total-space open set. -/
abbrev TotalSection (P : HolomorphicPeriodMap V B) (U : Opens P.TotalSpace) : Type :=
  letI := P.totalChartedSpace
  HolomorphicFunctionSheaf.Section IT P.TotalSpace U

/-- The literal inverse image of a total-space open in the original native torus. -/
abbrev fibrePreimage (P : HolomorphicPeriodMap V B) (b : B) (U : Opens P.TotalSpace) :=
  (Opens.map (fibreMap P b)).obj U

/-- Actual holomorphic sections on that original fibre open set. -/
abbrev FibreSection (P : HolomorphicPeriodMap V B) (b : B) (U : Opens P.TotalSpace) :=
  HolomorphicFunctionSheaf.Section I₂ (P.point b).Torus (fibrePreimage P b U)

/-- Literal restriction on the original total-space holomorphic sections. -/
def totalRestriction (P : HolomorphicPeriodMap V B) {U W : Opens P.TotalSpace} (h : U ≤ W) :
    TotalSection P W →ₐ[ℂ] TotalSection P U := by
  letI := P.totalChartedSpace
  exact HolomorphicFunctionSheaf.restrictionAlgHom IT P.TotalSpace h

/-- Literal restriction on the original fibre holomorphic sections. -/
def fibreRestriction (P : HolomorphicPeriodMap V B) (b : B)
    {U W : Opens P.TotalSpace} (h : U ≤ W) :
    FibreSection P b W →ₐ[ℂ] FibreSection P b U :=
  HolomorphicFunctionSheaf.restrictionAlgHom I₂ (P.point b).Torus (fun _ hx => h hx)

/-- The actual fibre holomorphic scalar endomorphism. -/
def fibreScalarEnd (P : HolomorphicPeriodMap V B) (b : B) (c : ℂ) :
    PeriodTorusHolomorphicCohomology.holomorphicSheaf (P.point b) ⟶
      PeriodTorusHolomorphicCohomology.holomorphicSheaf (P.point b) :=
  HolomorphicFunctionSheaf.scalarSheafEnd I₂ (P.point b).Torus c

variable [IsManifold (modelWithCornersSelf ℂ V) ω B]

/-- The original fibre inclusion as an actual holomorphic map into the unchanged family atlas. -/
def fibreHolomorphicMap (P : HolomorphicPeriodMap V B) (b : B) :
    letI := P.totalChartedSpace
    ContMDiffMap I₂ IT (P.point b).Torus P.TotalSpace ω := by
  letI := P.totalChartedSpace
  exact ⟨P.fibreInclusion b, P.fibreInclusion_holomorphic b⟩

/-- Actual algebra pullback on every original total-space open set. -/
def coefficientSection (P : HolomorphicPeriodMap V B) (b : B) (U : Opens P.TotalSpace) :
    TotalSection P U →ₐ[ℂ] FibreSection P b U := by
  letI := P.totalChartedSpace
  exact CuspNormalization.SheafOverBase.sectionPullback IT I₂
    (𝟙 (TopCat.of P.TotalSpace)) (fibreMap P b) (fibreHolomorphicMap P b) (fun _ => rfl) U

/-- The actual section map is literal composition with the original fibre inclusion. -/
@[simp] theorem coefficientSection_apply (P : HolomorphicPeriodMap V B) (b : B)
    (U : Opens P.TotalSpace) (s : TotalSection P U) (t : fibrePreimage P b U) :
    coefficientSection P b U s t = s ⟨fibreMap P b t, t.property⟩ := rfl

/-- The genuine coefficient morphism from the native total holomorphic
sheaf to the actual pushforward of the original fibre holomorphic sheaf. -/
def coefficientPullback (P : HolomorphicPeriodMap V B) (b : B) :
    Zero.totalAdditiveSheaf P ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat (fibreMap P b)).obj
        (PeriodTorusHolomorphicCohomology.holomorphicSheaf (P.point b)) := by
  letI := P.totalChartedSpace
  exact CuspNormalization.SheafOverBase.additivePullback IT I₂
    (𝟙 (TopCat.of P.TotalSpace)) (fibreMap P b) (fibreHolomorphicMap P b) (fun _ => rfl)

@[simp] theorem coefficientPullback_app (P : HolomorphicPeriodMap V B) (b : B)
    (U : Opens P.TotalSpace) (s : TotalSection P U) :
    (coefficientPullback P b).hom.app (op U) s = coefficientSection P b U s := rfl

/-- On every original open the coefficient map commutes with the actual restrictions. -/
theorem coefficientSection_restrict (P : HolomorphicPeriodMap V B) (b : B)
    {U W : Opens P.TotalSpace} (h : U ≤ W) (s : TotalSection P W) :
    coefficientSection P b U (totalRestriction P h s) =
      fibreRestriction P b h (coefficientSection P b W s) := by
  apply ContMDiffMap.ext
  intro t
  rfl

/-- Literal pointwise complex scalars are preserved on every open-set component. -/
theorem coefficientSection_smul (P : HolomorphicPeriodMap V B) (b : B)
    (U : Opens P.TotalSpace) (c : ℂ) (s : TotalSection P U) :
    coefficientSection P b U (c • s) = c • coefficientSection P b U s :=
  (coefficientSection P b U).toLinearMap.map_smul c s

/-- The original total and fibre scalar sheaf maps commute with the genuine coefficient pullback. -/
@[reassoc] theorem coefficientPullback_scalar (P : HolomorphicPeriodMap V B) (b : B) (c : ℂ) :
    Zero.totalScalarEnd P c ≫ coefficientPullback P b =
      coefficientPullback P b ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat (fibreMap P b)).map (fibreScalarEnd P b c) := by
  let := P.totalChartedSpace
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  apply ContMDiffMap.ext
  intro t
  rfl

/-- On a full base neighborhood, this section map is exactly the
previously proved restriction to the original compact complex fibre. -/
theorem coefficientSection_fullPreimage_apply (P : HolomorphicPeriodMap V B)
    (U : Opens B) (s : Zero.PreimageSection P U) (b : U) (t : (P.point b).Torus) :
    coefficientSection P b (Zero.basePreimage P U) s ⟨t, b.property⟩ =
      Zero.sectionOnFibre P U s b t := rfl

/-- The coefficient restriction of a genuine base pullback is its
literal value at the original base point. -/
theorem coefficientSection_basePullback_apply (P : HolomorphicPeriodMap V B)
    (U : Opens B) (f : Zero.BaseSection P U) (b : U) (t : (P.point b).Torus) :
    coefficientSection P b (Zero.basePreimage P U) (Zero.pullbackSection P U f)
      ⟨t, b.property⟩ = f b := rfl

/-- Restricting the original base-function action to the actual fibre
gives ordinary scalar multiplication by the base-point value. -/
theorem coefficientSection_fullPreimage_base_smul (P : HolomorphicPeriodMap V B)
    (U : Opens B) (a : Zero.BaseSection P U) (s : Zero.PreimageSection P U) (b : U) :
    coefficientSection P b (Zero.basePreimage P U) (a • s) =
      (a b) • coefficientSection P b (Zero.basePreimage P U) s := by
  apply ContMDiffMap.ext
  intro t
  rfl

end Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.FibreGeometry
