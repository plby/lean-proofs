import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRestrictionForward
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRestrictionInverse

/-!
# Native biholomorphic identification of a restricted period family

The source has the actual varying-period quotient atlas constructed from the
restricted original periods. The target is the literal full base preimage
with its inherited open-submanifold atlas. Both directions are proved
holomorphic through the original complex-vector covering maps.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.Restriction

open PeriodFamilyHigherDirectImage

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]
  [IsManifold (modelWithCornersSelf ℂ V) ω B]

local notation "IT" => modelWithCornersSelf ℂ (V × ComplexPlane₂)

/-- The actual restricted period family is biholomorphic to the full preimage
of the base open, with both original complex atlas constructions retained. -/
def restrictionBiholomorph (P : HolomorphicPeriodMap V B) (U : Opens B) :
    letI := (restrictedPeriods P U).totalChartedSpace
    letI := P.totalChartedSpace
    Diffeomorph IT IT (restrictedPeriods P U).TotalSpace (Zero.basePreimage P U) ω := by
  letI := (restrictedPeriods P U).totalChartedSpace
  letI := P.totalChartedSpace
  exact
    { toEquiv := (restrictionHomeomorph P U).toEquiv
      contMDiff_toFun := toPreimage_holomorphic P U
      contMDiff_invFun := fromPreimage_holomorphic P U }

@[simp] theorem restrictionBiholomorph_apply (P : HolomorphicPeriodMap V B) (U : Opens B)
    (x : (restrictedPeriods P U).TotalSpace) :
    restrictionBiholomorph P U x = toPreimage P U x := rfl

@[simp] theorem restrictionBiholomorph_val (P : HolomorphicPeriodMap V B) (U : Opens B)
    (x : (restrictedPeriods P U).TotalSpace) :
    (restrictionBiholomorph P U x : P.TotalSpace) = ((x.1 : B), x.2) := rfl

@[simp] theorem restrictionBiholomorph_symm_apply
    (P : HolomorphicPeriodMap V B) (U : Opens B) (x : Zero.basePreimage P U) :
    letI := (restrictedPeriods P U).totalChartedSpace
    letI := P.totalChartedSpace
    (restrictionBiholomorph P U).symm x = fromPreimage P U x := by
  let := (restrictedPeriods P U).totalChartedSpace
  let := P.totalChartedSpace
  rfl

/-- The analytic equivalence has exactly the original pair-regrouping homeomorphism. -/
theorem restrictionBiholomorph_toHomeomorph (P : HolomorphicPeriodMap V B) (U : Opens B) :
    letI := (restrictedPeriods P U).totalChartedSpace
    letI := P.totalChartedSpace
    (restrictionBiholomorph P U).toHomeomorph = restrictionHomeomorph P U := by
  let := (restrictedPeriods P U).totalChartedSpace
  let := P.totalChartedSpace
  apply Homeomorph.ext
  intro x
  rfl

/-- The biholomorphism commutes with the original complex-vector covering maps. -/
@[simp] theorem restrictionBiholomorph_quotientMap
    (P : HolomorphicPeriodMap V B) (U : Opens B) (x : U × ComplexPlane₂) :
    restrictionBiholomorph P U ((restrictedPeriods P U).quotientMap x) =
      (⟨P.quotientMap ((x.1 : B), x.2), x.1.property⟩ : Zero.basePreimage P U) := rfl

/-- The biholomorphism is over the literal original base open. -/
@[simp] theorem restrictionBiholomorph_projection
    (P : HolomorphicPeriodMap V B) (U : Opens B) (x : (restrictedPeriods P U).TotalSpace) :
    Zero.baseProjection P U (restrictionBiholomorph P U x) =
      (restrictedPeriods P U).projection x := rfl

/-- It preserves the original zero section, not just its image as a set. -/
@[simp] theorem restrictionBiholomorph_zeroSection
    (P : HolomorphicPeriodMap V B) (U : Opens B) (b : U) :
    restrictionBiholomorph P U ((restrictedPeriods P U).zeroSection b) =
      Zero.zeroSectionOn P U b := rfl

/-- It preserves each original complex period-torus inclusion. -/
@[simp] theorem restrictionBiholomorph_fibreInclusion
    (P : HolomorphicPeriodMap V B) (U : Opens B) (b : U) (z : (P.point b).Torus) :
    restrictionBiholomorph P U ((restrictedPeriods P U).fibreInclusion b z) =
      Zero.fibreOn P U b z := rfl

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.Restriction
