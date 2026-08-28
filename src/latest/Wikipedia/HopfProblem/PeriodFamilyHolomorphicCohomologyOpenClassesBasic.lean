import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRestriction
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyCocycle
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyHolomorphicRestrictionCohomology
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyBiholomorph

/-!
# Actual neighborhood cohomology and the original restricted period family

The neighborhood group is Mathlib's genuine cohomology-presheaf value
on the original full base preimage. Exact open restriction, the actual
holomorphic restriction sheaf isomorphism, and the original restriction
biholomorphism compare it with genuine cohomology of the original
restricted period family in every degree. Neither cohomology group nor
complex atlas is replaced by a definition of a different model.
-/

noncomputable section

open CategoryTheory TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClasses

open HolomorphicSheafCohomology

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]

local notation "IT" => modelWithCornersSelf ℂ (V × ComplexPlane₂)

/-- The original cohomology-presheaf group on the original full inverse
image of the base open. This is exactly Mathlib's actual `Sheaf.H'`. -/
abbrev neighborhoodCohomology (P : HolomorphicPeriodMap V B) (U : Opens B) (q : ℕ) :=
  CategoryTheory.Sheaf.H'.{0} (PeriodFamilyHigherDirectImage.Zero.totalAdditiveSheaf P)
    q (PeriodFamilyHigherDirectImage.Zero.basePreimage P U)

/-- The original holomorphic sheaf of the actual open submanifold,
with the atlas inherited from the original total-family quotient atlas. -/
def preimageHolomorphicSheaf (P : HolomorphicPeriodMap V B) (U : Opens B) :
    TopCat.Sheaf AddCommGrpCat
      (TopCat.of (PeriodFamilyHigherDirectImage.Zero.basePreimage P U)) := by
  letI := P.totalChartedSpace
  exact HolomorphicFunctionSheaf.additiveSheaf IT
    (PeriodFamilyHigherDirectImage.Zero.basePreimage P U)

/-- The original group structure of the native `Ext` group on this
actual open-submanifold holomorphic sheaf. -/
instance preimageCohomologyAddCommGroup (P : HolomorphicPeriodMap V B) (U : Opens B) (q : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H.{0} (preimageHolomorphicSheaf P U) q) :=
  CategoryTheory.Abelian.Ext.instAddCommGroup

/-- The actual ambient-open group is actual cohomology of its genuine
holomorphic open-submanifold sheaf. No separation hypothesis is needed. -/
def openCohomologyEquiv (P : HolomorphicPeriodMap V B) (U : Opens B) (q : ℕ) :
    neighborhoodCohomology P U q ≃+
      CategoryTheory.Sheaf.H.{0} (preimageHolomorphicSheaf P U) q := by
  letI := P.totalChartedSpace
  exact HolomorphicRestriction.cohomologyEquiv IT
    (PeriodFamilyHigherDirectImage.Zero.basePreimage P U) q

variable [IsManifold (modelWithCornersSelf ℂ V) ω B]

/-- The original restriction biholomorphism induces the genuine
cohomology comparison. Hausdorffness supplies the hypothesis of the
existing finite-closed-pushforward theorem; no compactness is assumed. -/
def restrictedFamilyCohomologyEquiv [T2Space B]
    (P : HolomorphicPeriodMap V B) (U : Opens B) (q : ℕ) :
    CategoryTheory.Sheaf.H.{0} (preimageHolomorphicSheaf P U) q ≃+
      CategoryTheory.Sheaf.H.{0} (PeriodFamilyHigherDirectImage.Zero.totalAdditiveSheaf
        (Restriction.restrictedPeriods P U)) q := by
  letI := (Restriction.restrictedPeriods P U).totalChartedSpace
  letI := P.totalChartedSpace
  exact Biholomorph.cohomologyEquiv (Restriction.restrictionBiholomorph P U) q

/-- The native all-degree neighborhood comparison with the actual
restricted period family, obtained from the proved original maps. -/
def neighborhoodCohomologyEquiv [T2Space B]
    (P : HolomorphicPeriodMap V B) (U : Opens B) (q : ℕ) :
    neighborhoodCohomology P U q ≃+
      CategoryTheory.Sheaf.H.{0} (PeriodFamilyHigherDirectImage.Zero.totalAdditiveSheaf
        (Restriction.restrictedPeriods P U)) q :=
  (openCohomologyEquiv P U q).trans (restrictedFamilyCohomologyEquiv P U q)

/-- The actual forward comparison is the stated composite of genuine
open restriction and the original biholomorphic comparison. -/
theorem neighborhoodCohomologyEquiv_apply [T2Space B]
    (P : HolomorphicPeriodMap V B) (U : Opens B) (q : ℕ)
    (x : neighborhoodCohomology P U q) :
    neighborhoodCohomologyEquiv P U q x =
      restrictedFamilyCohomologyEquiv P U q (openCohomologyEquiv P U q x) := rfl

/-- The inverse returns to the original native neighborhood group,
using inverses of the same proved genuine comparisons. -/
theorem neighborhoodCohomologyEquiv_symm_apply [T2Space B]
    (P : HolomorphicPeriodMap V B) (U : Opens B) (q : ℕ)
    (x : CategoryTheory.Sheaf.H.{0} (PeriodFamilyHigherDirectImage.Zero.totalAdditiveSheaf
      (Restriction.restrictedPeriods P U)) q) :
    (neighborhoodCohomologyEquiv P U q).symm x =
      (openCohomologyEquiv P U q).symm ((restrictedFamilyCohomologyEquiv P U q).symm x) := rfl

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClasses
