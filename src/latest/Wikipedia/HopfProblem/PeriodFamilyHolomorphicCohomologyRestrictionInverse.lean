import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRestrictionBasic
import Wikipedia.HopfProblem.CuspPuncturedManifold

/-!
# The inverse restriction map in the original period-family atlases

The original complex-vector quotient covering restricts to a surjective local
biholomorphism onto the full base preimage. Pulling back the inverse restriction
map along this covering gives precisely the restricted period family's own
complex-vector quotient map. Holomorphicity therefore descends without changing
the inherited open-submanifold atlas or either period-family quotient atlas.
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
local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂

local instance inverseCoveringChartedSpace :
    ChartedSpace (V × ComplexPlane₂) (B × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd V ComplexPlane₂) (B × ComplexPlane₂))

local instance inverseCoveringManifold [IsManifold IB ω B] :
    IsManifold IT ω (B × ComplexPlane₂) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := IB) (I' := I₂) B ComplexPlane₂

/-- The native complex-vector covering restricted over the chosen base open. -/
def inverseCoveringOpen (U : Opens B) : Opens (B × ComplexPlane₂) :=
  ⟨Prod.fst ⁻¹' (U : Set B), U.isOpen.preimage continuous_fst⟩

/-- The literal restriction of the original quotient covering map. -/
def inverseCoveringProjection (P : HolomorphicPeriodMap V B) (U : Opens B) :
    inverseCoveringOpen U → Zero.basePreimage P U :=
  fun a => ⟨P.quotientMap a.val, a.property⟩

/-- Regroup the same original complex coordinates over the open base. -/
def inverseCoveringRestriction (U : Opens B) :
    inverseCoveringOpen U → U × ComplexPlane₂ :=
  fun a => (⟨a.val.1, a.property⟩, a.val.2)

/-- Every point of the full preimage has an original complex-vector lift. -/
theorem inverseCoveringProjection_surjective (P : HolomorphicPeriodMap V B)
    (U : Opens B) : Function.Surjective (inverseCoveringProjection P U) := by
  intro x
  obtain ⟨a, ha⟩ := P.quotientMap_surjective x.val
  refine ⟨⟨a, ?_⟩, Subtype.ext ha⟩
  change P.projection (P.quotientMap a) ∈ U
  rw [ha]
  exact x.property

/-- The inverse restriction square commutes on literal covering coordinates. -/
@[simp] theorem fromPreimage_inverseCoveringProjection
    (P : HolomorphicPeriodMap V B) (U : Opens B) (a : inverseCoveringOpen U) :
    fromPreimage P U (inverseCoveringProjection P U a) =
      (restrictedPeriods P U).quotientMap (inverseCoveringRestriction U a) := rfl

/-- The covering-coordinate regrouping is holomorphic in the inherited open charts. -/
theorem inverseCoveringRestriction_holomorphic (U : Opens B) :
    ContMDiff IT IT ω (inverseCoveringRestriction U) := by
  rw [modelWithCornersSelf_prod]
  have hf : ContMDiff ((IB).prod I₂) IB ω
      (fun a : inverseCoveringOpen U => a.val.1) :=
    contMDiff_fst.comp contMDiff_subtype_val
  have hb : ContMDiff ((IB).prod I₂) IB ω
      (fun a : inverseCoveringOpen U => (inverseCoveringRestriction U a).1) := by
    intro a
    have he : ContMDiffAt ((IB).prod I₂) IB ω
        (fun y : inverseCoveringOpen U => ((inverseCoveringRestriction U y).1 : B)) a ↔
        ContMDiffAt ((IB).prod I₂) IB ω
          (fun y : inverseCoveringOpen U => (inverseCoveringRestriction U y).1) a :=
      ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
    exact he.mp (hf a)
  exact hb.prodMk (contMDiff_snd.comp contMDiff_subtype_val)

variable [IsManifold (modelWithCornersSelf ℂ V) ω B]

/-- The original covering remains locally biholomorphic after open restriction. -/
theorem inverseCoveringProjection_isLocalDiffeomorph
    (P : HolomorphicPeriodMap V B) (U : Opens B) :
    letI := P.totalChartedSpace
    IsLocalDiffeomorph IT IT ω (inverseCoveringProjection P U) := by
  let := P.coveringAction
  let := P.totalChartedSpace
  have hq : IsLocalDiffeomorph IT IT ω P.quotientMap :=
    CoveringQuotient.project_isLocalDiffeomorph (E := V × ComplexPlane₂)
      P.quotientCoveringMap P.coveringAction_holomorphic
  exact isLocalDiffeomorph_restrictOpens IT IT hq
    (inverseCoveringOpen U) (Zero.basePreimage P U) (fun _ ha => ha)

/-- The literal inverse restriction is holomorphic for both original quotient atlases. -/
theorem fromPreimage_holomorphic (P : HolomorphicPeriodMap V B) (U : Opens B) :
    letI := P.totalChartedSpace
    letI := (restrictedPeriods P U).totalChartedSpace
    ContMDiff IT IT ω (fromPreimage P U) := by
  let := P.totalChartedSpace
  let := (restrictedPeriods P U).totalChartedSpace
  apply contMDiff_of_comp_localDiffeomorph IT IT IT
    (inverseCoveringProjection_isLocalDiffeomorph P U)
    (inverseCoveringProjection_surjective P U)
  change ContMDiff IT IT ω
    ((restrictedPeriods P U).quotientMap ∘ inverseCoveringRestriction U)
  exact (restrictedPeriods P U).quotientMap_holomorphic.comp
    (inverseCoveringRestriction_holomorphic U)

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.Restriction
