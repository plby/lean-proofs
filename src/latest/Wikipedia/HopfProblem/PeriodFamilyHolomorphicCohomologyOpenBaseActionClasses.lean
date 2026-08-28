import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenBaseActionActions
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenBaseActionComparison
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassesClasses

/-!
# Genuine base-open linearity of native neighborhood period classes

The original restriction biholomorphism preserves the literal base
projection, hence the original coefficient multipliers. Its genuine
cohomology comparison therefore preserves the independently defined
base-function actions. The existing native neighborhood period classes
are linear over the original holomorphic functions on the base open.
No assertion about generation or a frame is made here.
-/

noncomputable section

open CategoryTheory TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenBaseAction

open PeriodFamilyHigherDirectImage

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]
  [IsManifold (modelWithCornersSelf ℂ V) ω B] [T2Space B]

/-- The genuine neighborhood comparison retains the actual coefficient
action of every original holomorphic base-open function. -/
theorem neighborhoodCohomologyEquiv_base_smul_map
    (P : HolomorphicPeriodMap V B) (U : Opens B) (q : ℕ)
    (g : Zero.BaseSection P U) (x : OpenClasses.neighborhoodCohomology P U q) :
    letI := neighborhoodCohomologyModule P U q
    OpenClasses.neighborhoodCohomologyEquiv P U q (g • x) =
      CategoryTheory.Sheaf.H.map
        (BaseFunctionAction.baseMultiplyEnd (Restriction.restrictedPeriods P U) g) q
        (OpenClasses.neighborhoodCohomologyEquiv P U q x) := by
  let := neighborhoodCohomologyModule P U q
  exact (congrArg (OpenClasses.restrictedFamilyCohomologyEquiv P U q)
    (openCohomologyEquiv_smul_map P U q g x)).trans
      (restrictedFamilyCohomologyEquiv_baseMultiply P U q g
        (OpenClasses.openCohomologyEquiv P U q x))

/-- Both modules are the original coefficient-induced actions, and
the actual comparison respects them for every native cohomology degree. -/
theorem neighborhoodCohomologyEquiv_base_smul
    (P : HolomorphicPeriodMap V B) (U : Opens B) (q : ℕ)
    (g : Zero.BaseSection P U) (x : OpenClasses.neighborhoodCohomology P U q) :
    letI := neighborhoodCohomologyModule P U q
    letI := BaseFunctionAction.baseCohomologyModule (Restriction.restrictedPeriods P U) q
    OpenClasses.neighborhoodCohomologyEquiv P U q (g • x) =
      g • OpenClasses.neighborhoodCohomologyEquiv P U q x :=
  neighborhoodCohomologyEquiv_base_smul_map P U q g x

/-- The actual all-degree neighborhood comparison is linear over
the ring of original holomorphic functions on the original base open. -/
def neighborhoodCohomologyBaseLinearEquiv
    (P : HolomorphicPeriodMap V B) (U : Opens B) (q : ℕ) :
    letI := neighborhoodCohomologyModule P U q
    letI := BaseFunctionAction.baseCohomologyModule (Restriction.restrictedPeriods P U) q
    OpenClasses.neighborhoodCohomology P U q ≃ₗ[Zero.BaseSection P U]
      CategoryTheory.Sheaf.H.{0}
        (Zero.totalAdditiveSheaf (Restriction.restrictedPeriods P U)) q := by
  letI := neighborhoodCohomologyModule P U q
  letI := BaseFunctionAction.baseCohomologyModule (Restriction.restrictedPeriods P U) q
  exact { OpenClasses.neighborhoodCohomologyEquiv P U q with
    map_smul' := neighborhoodCohomologyEquiv_base_smul P U q }

/-- The existing genuine native neighborhood period class respects
the actual holomorphic base-open action on its original cohomology group. -/
theorem periodClass_base_smul (P : HolomorphicPeriodMap V B) (U : Opens B)
    (g : Zero.BaseSection P U) (a : OpenClasses.Coefficients (V := V) U) :
    letI := neighborhoodCohomologyModule P U 1
    OpenClasses.periodClass P U (g • a) = g • OpenClasses.periodClass P U a := by
  let := neighborhoodCohomologyModule P U 1
  apply (OpenClasses.neighborhoodCohomologyEquiv P U 1).injective
  exact (OpenClasses.periodClass_comparison P U (g • a)).trans
    ((BaseFunctionAction.periodClass_mul_base (Restriction.restrictedPeriods P U) g a).trans
      ((congrArg (CategoryTheory.Sheaf.H.map
        (BaseFunctionAction.baseMultiplyEnd (Restriction.restrictedPeriods P U) g) 1)
        (OpenClasses.periodClass_comparison P U a).symm).trans
          (neighborhoodCohomologyEquiv_base_smul_map P U 1 g
            (OpenClasses.periodClass P U a)).symm))

/-- The original neighborhood period-class map is linear over actual
holomorphic base-open functions, with its coefficient-induced target module. -/
def periodClassBaseLinearMap (P : HolomorphicPeriodMap V B) (U : Opens B) :
    letI := neighborhoodCohomologyModule P U 1
    OpenClasses.Coefficients (V := V) U →ₗ[Zero.BaseSection P U]
      OpenClasses.neighborhoodCohomology P U 1 := by
  letI := neighborhoodCohomologyModule P U 1
  exact { OpenClasses.periodClassHom P U with map_smul' := periodClass_base_smul P U }

@[simp] theorem periodClassBaseLinearMap_apply (P : HolomorphicPeriodMap V B) (U : Opens B)
    (a : OpenClasses.Coefficients (V := V) U) :
    letI := neighborhoodCohomologyModule P U 1
    periodClassBaseLinearMap P U a = OpenClasses.periodClass P U a := rfl

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenBaseAction
