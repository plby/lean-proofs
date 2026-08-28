import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRestrictionBasic

/-!
# Holomorphicity of the native restricted-family inclusion

The pair-regrouping map is proved holomorphic by composing with the actual
complex-vector quotient covering of the restricted family.  The resulting
map is the original quotient map composed with the open inclusion on the
complex base.  Both total-space atlases remain their originally constructed
varying-period quotient atlases.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.Restriction

open PeriodFamilyHigherDirectImage

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]

local notation "IB" => modelWithCornersSelf ℂ V
local notation "IT" => modelWithCornersSelf ℂ (V × ComplexPlane₂)

local instance forwardCoveringChartedSpace {A : Type*} [TopologicalSpace A]
    [ChartedSpace V A] : ChartedSpace (V × ComplexPlane₂) (A × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd V ComplexPlane₂) (A × ComplexPlane₂))

local instance forwardCoveringManifold {A : Type*} [TopologicalSpace A]
    [ChartedSpace V A] [IsManifold IB ω A] : IsManifold IT ω (A × ComplexPlane₂) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := IB) (I' := modelWithCornersSelf ℂ ComplexPlane₂) A ComplexPlane₂

/-- The literal open inclusion on the complex-vector covering spaces. -/
def coverInclusion (U : Opens B) : U × ComplexPlane₂ → B × ComplexPlane₂ :=
  fun x => ((x.1 : B), x.2)

/-- This inclusion is holomorphic in the genuine product complex covering atlases. -/
theorem coverInclusion_holomorphic (U : Opens B) :
    ContMDiff IT IT ω (coverInclusion U) := by
  rw [modelWithCornersSelf_prod]
  exact (contMDiff_subtype_val.comp contMDiff_fst).prodMk contMDiff_snd

variable [IsManifold (modelWithCornersSelf ℂ V) ω B]

/-- Holomorphicity in the original ambient total-space atlas descends through
the actual restricted-period covering. -/
theorem toPreimage_val_holomorphic (P : HolomorphicPeriodMap V B) (U : Opens B) :
    letI := (restrictedPeriods P U).totalChartedSpace
    letI := P.totalChartedSpace
    ContMDiff IT IT ω (fun x => (toPreimage P U x : P.TotalSpace)) := by
  let := (restrictedPeriods P U).totalChartedSpace
  let := P.totalChartedSpace
  let := (restrictedPeriods P U).coveringAction
  apply CoveringQuotient.contMDiff_of_comp (E := V × ComplexPlane₂)
    (restrictedPeriods P U).quotientCoveringMap IT ω
  exact (P.quotientMap_holomorphic.comp (coverInclusion_holomorphic U)).congr
    (fun x => congrArg Subtype.val (toPreimage_quotientMap P U x))

/-- The forward identification is holomorphic into the actual inherited
open-submanifold atlas on the original full preimage. -/
theorem toPreimage_holomorphic (P : HolomorphicPeriodMap V B) (U : Opens B) :
    letI := (restrictedPeriods P U).totalChartedSpace
    letI := P.totalChartedSpace
    ContMDiff IT IT ω (toPreimage P U) := by
  let := (restrictedPeriods P U).totalChartedSpace
  let := P.totalChartedSpace
  intro x
  have h : ContMDiffAt IT IT ω
      (fun y => (toPreimage P U y : P.TotalSpace)) x ↔
      ContMDiffAt IT IT ω (toPreimage P U) x :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact h.mp (toPreimage_val_holomorphic P U x)

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.Restriction
