import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageStalkBaseActionBasic
import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageStalkNaturalityGerms
import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImagePeriodClasses

/-!
# Original period-class germs respect the genuine derived-stalk actions

Coefficient naturality of the original neighborhood comparison shows
that global cohomology germs respect the native complex and global
holomorphic base actions. The original period-class maps are therefore
linear for these independently defined actions. Their underlying
extension classes, stalk germs, and marked constants remain unchanged.
-/

noncomputable section

open CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.StalkBaseAction

open PeriodFamilyHolomorphicCohomology
open PeriodFamilyHolomorphicCohomology.BaseFunctionAction

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]
  [IsManifold (modelWithCornersSelf ℂ V) ω B]

/-- Original global cohomology germs preserve the genuine global-base
action on source and on the actual right-derived stalk. -/
theorem globalStalkClass_base_smul (P : HolomorphicPeriodMap V B) (b : B) (q : ℕ)
    (g : BaseFunction V B)
    (a : CategoryTheory.Sheaf.H.{0} (Zero.totalAdditiveSheaf P) q) :
    letI := baseCohomologyModule P q
    letI := stalkBaseModule P b q
    GlobalRestriction.globalStalkClass (Zero.projectionMap P) (Zero.totalAdditiveSheaf P)
        b q (g • a) =
      g • GlobalRestriction.globalStalkClass (Zero.projectionMap P) (Zero.totalAdditiveSheaf P)
        b q a :=
  (StalkNaturality.globalStalkClass_naturality
    (Zero.projectionMap P) (baseMultiplyEnd P g) b q a).symm

omit [IsManifold (modelWithCornersSelf ℂ V) ω B] in
/-- Original global cohomology germs preserve the independently
coefficient-induced complex actions. -/
theorem globalStalkClass_complex_smul (P : HolomorphicPeriodMap V B) (b : B) (q : ℕ)
    (c : ℂ) (a : CategoryTheory.Sheaf.H.{0} (Zero.totalAdditiveSheaf P) q) :
    letI := Cocycle.totalCohomologyModule P q
    letI := stalkComplexModule P b q
    GlobalRestriction.globalStalkClass (Zero.projectionMap P) (Zero.totalAdditiveSheaf P)
        b q (c • a) =
      c • GlobalRestriction.globalStalkClass (Zero.projectionMap P) (Zero.totalAdditiveSheaf P)
        b q a :=
  (StalkNaturality.globalStalkClass_naturality
    (Zero.projectionMap P) (Zero.totalScalarEnd P c) b q a).symm

/-- The genuine global-cohomology germ map over actual holomorphic base functions. -/
def globalStalkClassBaseLinearMap (P : HolomorphicPeriodMap V B) (b : B) (q : ℕ) :
    letI := baseCohomologyModule P q
    letI := stalkBaseModule P b q
    CategoryTheory.Sheaf.H.{0} (Zero.totalAdditiveSheaf P) q →ₗ[BaseFunction V B]
      higherDirectImageStalk P b q := by
  letI := baseCohomologyModule P q
  letI := stalkBaseModule P b q
  exact { GlobalRestriction.globalStalkClass
    (Zero.projectionMap P) (Zero.totalAdditiveSheaf P) b q with
    map_smul' := globalStalkClass_base_smul P b q }

/-- The same original global germ map with its independent complex actions. -/
def globalStalkClassLinearMap (P : HolomorphicPeriodMap V B) (b : B) (q : ℕ) :
    letI := Cocycle.totalCohomologyModule P q
    letI := stalkComplexModule P b q
    CategoryTheory.Sheaf.H.{0} (Zero.totalAdditiveSheaf P) q →ₗ[ℂ]
      higherDirectImageStalk P b q := by
  letI := Cocycle.totalCohomologyModule P q
  letI := stalkComplexModule P b q
  exact { GlobalRestriction.globalStalkClass
    (Zero.projectionMap P) (Zero.totalAdditiveSheaf P) b q with
    map_smul' := globalStalkClass_complex_smul P b q }

/-- The actual period-class germ map is linear over original global
holomorphic base functions, with its original native target action. -/
def periodStalkClassBaseLinearMap (P : HolomorphicPeriodMap V B) (b : B) :
    letI := stalkBaseModule P b 1
    Cocycle.Coefficients V B →ₗ[BaseFunction V B] higherDirectImageStalk P b 1 := by
  letI := baseCohomologyModule P 1
  letI := stalkBaseModule P b 1
  exact (globalStalkClassBaseLinearMap P b 1).comp (periodClassBaseLinearMap P)

@[simp] theorem periodStalkClassBaseLinearMap_apply (P : HolomorphicPeriodMap V B)
    (b : B) (a : Cocycle.Coefficients V B) :
    letI := stalkBaseModule P b 1
    periodStalkClassBaseLinearMap P b a = periodStalkClass P b a := rfl

/-- The same genuine period-class germ map is complex-linear. -/
def periodStalkClassLinearMap (P : HolomorphicPeriodMap V B) (b : B) :
    letI := stalkComplexModule P b 1
    Cocycle.Coefficients V B →ₗ[ℂ] higherDirectImageStalk P b 1 := by
  letI := Cocycle.totalCohomologyModule P 1
  letI := stalkComplexModule P b 1
  exact (globalStalkClassLinearMap P b 1).comp (Cocycle.periodClassLinearMap P)

@[simp] theorem periodStalkClassLinearMap_apply (P : HolomorphicPeriodMap V B)
    (b : B) (a : Cocycle.Coefficients V B) :
    letI := stalkComplexModule P b 1
    periodStalkClassLinearMap P b a = periodStalkClass P b a := rfl

/-- The original two marked constant-character germs form an actual
complex-linear map into the genuine derived stalk. -/
def firstPeriodStalkClassLinearMap (P : HolomorphicPeriodMap V B) (b : B) :
    letI := stalkComplexModule P b 1
    (Fin 2 → ℂ) →ₗ[ℂ] higherDirectImageStalk P b 1 := by
  letI := stalkComplexModule P b 1
  exact (periodStalkClassLinearMap P b).comp
    (constantPeriodCoefficients.comp MarkedLinear.firstCoefficients)

@[simp] theorem firstPeriodStalkClassLinearMap_apply (P : HolomorphicPeriodMap V B)
    (b : B) (c : Fin 2 → ℂ) :
    letI := stalkComplexModule P b 1
    firstPeriodStalkClassLinearMap P b c = firstPeriodStalkClass P b c := rfl

end Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.StalkBaseAction
