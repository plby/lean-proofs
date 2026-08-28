import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageFibreComparison
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyBaseFunctionAction
import Wikipedia.HopfProblem.SheafLerayLowDegreesScalarsDerivedAdditive

/-!
# Original global base functions acting on genuine derived stalks

The native right-derived pushforward and the native stalk functor send
the original coefficient multipliers to endomorphisms of the actual
higher-direct-image stalk. Their evaluation gives the action of global
holomorphic base functions. The independent complex action is obtained
from the original constant coefficient multipliers, and the two agree
on constants.

No action is transported through a cohomology comparison or a basis.
This file concerns global base functions, not yet the full local ring
of holomorphic germs, and asserts neither local generation nor base change.
-/

noncomputable section

open CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.StalkBaseAction

open PeriodFamilyHolomorphicCohomology.BaseFunctionAction
open CuspNormalization.SheafCohomology

/-- The actual composite of native right-derived pushforward, underlying
presheaf, and native stalk functors, with no comparison isomorphism. -/
abbrev nativeStalkFunctor {X Y : TopCat.{0}} (f : X ⟶ Y) (y : Y) (q : ℕ) :
    SheafHigherDirectImage.AbelianSheaf X ⥤ AddCommGrpCat.{0} :=
  SheafHigherDirectImage.functor f q ⋙ TopCat.Sheaf.forget AddCommGrpCat Y ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat y

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]

/-- The original constant coefficient multipliers in the unchanged total atlas. -/
def totalComplexScalarEnd (P : HolomorphicPeriodMap V B) :
    ℂ →+* End (Zero.totalAdditiveSheaf P) := by
  letI := P.totalChartedSpace
  exact holomorphicScalarEnd (modelWithCornersSelf ℂ (V × ComplexPlane₂)) P.TotalSpace

@[simp] theorem totalComplexScalarEnd_apply (P : HolomorphicPeriodMap V B) (c : ℂ) :
    totalComplexScalarEnd P c = Zero.totalScalarEnd P c := rfl

/-- The original complex scalar endomorphisms after the genuine derived
pushforward and stalk functors. -/
def stalkComplexEnd (P : HolomorphicPeriodMap V B) (b : B) (q : ℕ) :
    ℂ →+* End (higherDirectImageStalk P b q) :=
  (mapEndRingHom (nativeStalkFunctor (Zero.projectionMap P) b q)
    (Zero.totalAdditiveSheaf P)).comp (totalComplexScalarEnd P)

/-- Complex multiplication on the actual derived stalk, induced by
the original constant coefficient maps. -/
@[instance_reducible] def stalkComplexModule (P : HolomorphicPeriodMap V B)
    (b : B) (q : ℕ) : Module ℂ (higherDirectImageStalk P b q) :=
  moduleOfScalarEnd (higherDirectImageStalk P b q) (stalkComplexEnd P b q)

/-- The complex action uses precisely the actual native stalk map. -/
theorem stalkComplexModule_smul (P : HolomorphicPeriodMap V B) (b : B) (q : ℕ)
    (c : ℂ) (x : higherDirectImageStalk P b q) :
    letI := stalkComplexModule P b q
    c • x = (TopCat.Presheaf.stalkFunctor AddCommGrpCat b).map
      ((SheafHigherDirectImage.functor (Zero.projectionMap P) q).map
        (Zero.totalScalarEnd P c)).hom x := rfl

variable [IsManifold (modelWithCornersSelf ℂ V) ω B]

/-- The actual global base-function coefficient action after the genuine
right-derived and stalk functors. -/
def stalkBaseEnd (P : HolomorphicPeriodMap V B) (b : B) (q : ℕ) :
    BaseFunction V B →+* End (higherDirectImageStalk P b q) :=
  (mapEndRingHom (nativeStalkFunctor (Zero.projectionMap P) b q)
    (Zero.totalAdditiveSheaf P)).comp (baseMultiplyRingHom P)

/-- Global holomorphic base functions act through their original
coefficient endomorphisms on the actual higher-direct-image stalk. -/
@[instance_reducible] def stalkBaseModule (P : HolomorphicPeriodMap V B)
    (b : B) (q : ℕ) : Module (BaseFunction V B) (higherDirectImageStalk P b q) :=
  moduleOfScalarEnd (higherDirectImageStalk P b q) (stalkBaseEnd P b q)

/-- The action is exactly the native stalk of the native right-derived
image of the original base multiplier. -/
theorem stalkBaseModule_smul (P : HolomorphicPeriodMap V B) (b : B) (q : ℕ)
    (g : BaseFunction V B) (x : higherDirectImageStalk P b q) :
    letI := stalkBaseModule P b q
    g • x = (TopCat.Presheaf.stalkFunctor AddCommGrpCat b).map
      ((SheafHigherDirectImage.functor (Zero.projectionMap P) q).map
        (baseMultiplyEnd P g)).hom x := rfl

/-- Constant global base functions give the independently defined
original complex coefficient action. -/
theorem stalkBaseEnd_algebraMap (P : HolomorphicPeriodMap V B) (b : B) (q : ℕ)
    (c : ℂ) :
    stalkBaseEnd P b q (algebraMap ℂ (BaseFunction V B) c) = stalkComplexEnd P b q c :=
  congrArg (fun k => (nativeStalkFunctor (Zero.projectionMap P) b q).map k)
    (baseMultiplyEnd_algebraMap P c)

/-- Agreement of the two genuine actions on complex constants. -/
theorem stalkBaseModule_algebraMap_smul (P : HolomorphicPeriodMap V B)
    (b : B) (q : ℕ) (c : ℂ) (x : higherDirectImageStalk P b q) :
    letI := stalkComplexModule P b q
    letI := stalkBaseModule P b q
    algebraMap ℂ (BaseFunction V B) c • x = c • x :=
  congrArg (fun k : End (higherDirectImageStalk P b q) => k.asHom x)
    (stalkBaseEnd_algebraMap P b q c)

/-- The original complex and global holomorphic base actions form
their natural scalar tower on the genuine derived stalk. -/
theorem stalkBaseScalarTower (P : HolomorphicPeriodMap V B) (b : B) (q : ℕ) :
    letI := stalkComplexModule P b q
    letI := stalkBaseModule P b q
    IsScalarTower ℂ (BaseFunction V B) (higherDirectImageStalk P b q) := by
  let := stalkComplexModule P b q
  let := stalkBaseModule P b q
  exact IsScalarTower.of_algebraMap_smul (stalkBaseModule_algebraMap_smul P b q)

end Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.StalkBaseAction
