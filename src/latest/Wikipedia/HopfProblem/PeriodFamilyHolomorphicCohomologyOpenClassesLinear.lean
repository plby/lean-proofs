import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassesActions
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassesClasses
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassesScalar

/-!
# Native complex-linearity of the all-open period class construction

The actual neighborhood comparison preserves the original scalar
cohomology-presheaf maps and the original restricted-family scalar
cohomology maps. Both module structures are independently induced by
the original sheaf scalar endomorphisms. The comparison and the actual
period-class construction are consequently genuine complex-linear maps.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClasses

open HolomorphicSheafCohomology

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]
  [IsManifold (modelWithCornersSelf ℂ V) ω B] [T2Space B]

local notation "IT" => modelWithCornersSelf ℂ (V × ComplexPlane₂)

/-- The all-degree neighborhood comparison commutes with the actual
coefficient scalar maps on both original native cohomology groups. -/
theorem neighborhoodCohomologyEquiv_scalar_map (P : HolomorphicPeriodMap V B)
    (U : Opens B) (q : ℕ) (c : ℂ) (x : neighborhoodCohomology P U q) :
    neighborhoodCohomologyEquiv P U q
        ((((CategoryTheory.Sheaf.cohomologyPresheafFunctor
          (Opens.grothendieckTopology (TopCat.of P.TotalSpace)) q).map
            (PeriodFamilyHigherDirectImage.Zero.totalScalarEnd P c)).app
          (op (PeriodFamilyHigherDirectImage.Zero.basePreimage P U))) x) =
      CategoryTheory.Sheaf.H.map
        (PeriodFamilyHigherDirectImage.Zero.totalScalarEnd
          (Restriction.restrictedPeriods P U) c) q (neighborhoodCohomologyEquiv P U q x) := by
  let := (Restriction.restrictedPeriods P U).totalChartedSpace
  let := P.totalChartedSpace
  exact (congrArg (restrictedFamilyCohomologyEquiv P U q)
    (holomorphicRestriction_cohomologyEquiv_scalar IT
      (PeriodFamilyHigherDirectImage.Zero.basePreimage P U) q c x)).trans
        (biholomorph_cohomologyEquiv_scalar (Restriction.restrictionBiholomorph P U)
          q c (openCohomologyEquiv P U q x))

/-- The proved comparison preserves the independently defined original
sheaf-induced scalar module structures. -/
theorem neighborhoodCohomologyEquiv_smul (P : HolomorphicPeriodMap V B)
    (U : Opens B) (q : ℕ) (c : ℂ) (x : neighborhoodCohomology P U q) :
    letI := neighborhoodCohomologyModule P U q
    letI := Cocycle.totalCohomologyModule (Restriction.restrictedPeriods P U) q
    neighborhoodCohomologyEquiv P U q (c • x) = c • neighborhoodCohomologyEquiv P U q x :=
  neighborhoodCohomologyEquiv_scalar_map P U q c x

/-- A genuine complex-linear equivalence between the original native
groups, with scalars coming from their actual sheaf endomorphisms. -/
def neighborhoodCohomologyLinearEquiv (P : HolomorphicPeriodMap V B) (U : Opens B) (q : ℕ) :
    letI := neighborhoodCohomologyModule P U q
    letI := Cocycle.totalCohomologyModule (Restriction.restrictedPeriods P U) q
    neighborhoodCohomology P U q ≃ₗ[ℂ]
      CategoryTheory.Sheaf.H.{0} (PeriodFamilyHigherDirectImage.Zero.totalAdditiveSheaf
        (Restriction.restrictedPeriods P U)) q := by
  letI := neighborhoodCohomologyModule P U q
  letI := Cocycle.totalCohomologyModule (Restriction.restrictedPeriods P U) q
  exact { neighborhoodCohomologyEquiv P U q with
    map_smul' := neighborhoodCohomologyEquiv_smul P U q }

@[simp] theorem neighborhoodCohomologyLinearEquiv_apply (P : HolomorphicPeriodMap V B)
    (U : Opens B) (q : ℕ) (x : neighborhoodCohomology P U q) :
    letI := neighborhoodCohomologyModule P U q
    letI := Cocycle.totalCohomologyModule (Restriction.restrictedPeriods P U) q
    neighborhoodCohomologyLinearEquiv P U q x = neighborhoodCohomologyEquiv P U q x := rfl

/-- The original neighborhood period class commutes with the genuine
cohomology-presheaf map of the actual original scalar endomorphism. -/
theorem periodClass_smul_map (P : HolomorphicPeriodMap V B) (U : Opens B)
    (c : ℂ) (a : Coefficients (V := V) U) :
    periodClass P U (c • a) =
      (((CategoryTheory.Sheaf.cohomologyPresheafFunctor
        (Opens.grothendieckTopology (TopCat.of P.TotalSpace)) 1).map
          (PeriodFamilyHigherDirectImage.Zero.totalScalarEnd P c)).app
        (op (PeriodFamilyHigherDirectImage.Zero.basePreimage P U))) (periodClass P U a) := by
  apply (neighborhoodCohomologyEquiv P U 1).injective
  exact (periodClass_comparison P U (c • a)).trans
    ((Cocycle.periodClass_smul_map (Restriction.restrictedPeriods P U) c a).trans
      ((congrArg (CategoryTheory.Sheaf.H.map
        (PeriodFamilyHigherDirectImage.Zero.totalScalarEnd
          (Restriction.restrictedPeriods P U) c) 1)
        (periodClass_comparison P U a).symm).trans
          (neighborhoodCohomologyEquiv_scalar_map P U 1 c (periodClass P U a)).symm))

/-- Complex-linearity uses the original native neighborhood action,
not a module structure introduced by the comparison. -/
theorem periodClass_smul (P : HolomorphicPeriodMap V B) (U : Opens B)
    (c : ℂ) (a : Coefficients (V := V) U) :
    letI := neighborhoodCohomologyModule P U 1
    periodClass P U (c • a) = c • periodClass P U a := periodClass_smul_map P U c a

/-- Actual holomorphic coefficients map complex-linearly into the
original cohomology-presheaf group on the actual full base preimage. -/
def periodClassLinearMap (P : HolomorphicPeriodMap V B) (U : Opens B) :
    letI := neighborhoodCohomologyModule P U 1
    Coefficients (V := V) U →ₗ[ℂ] neighborhoodCohomology P U 1 := by
  letI := neighborhoodCohomologyModule P U 1
  exact { periodClassHom P U with map_smul' := periodClass_smul P U }

@[simp] theorem periodClassLinearMap_apply (P : HolomorphicPeriodMap V B) (U : Opens B)
    (a : Coefficients (V := V) U) :
    letI := neighborhoodCohomologyModule P U 1
    periodClassLinearMap P U a = periodClass P U a := rfl

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClasses
