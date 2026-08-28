import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyCocycleCoverBasic

/-!
# Holomorphicity of the actual local lifts in the original family atlas

The upstairs atlas is the ordinary product of the given base atlas
with the covering vector space. The downstairs atlas is precisely the
original varying-period quotient atlas. The proved quotient-cover
local-inverse theorem makes each literal covering lift holomorphic.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.Cocycle

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]

local notation "IB" => modelWithCornersSelf ℂ V
local notation "IT" => modelWithCornersSelf ℂ (V × ComplexPlane₂)

/-- The actual upstairs product atlas used by the original period-family construction. -/
@[instance_reducible] def coverChartedSpace :
    ChartedSpace (V × ComplexPlane₂) (B × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd V ComplexPlane₂) (B × ComplexPlane₂))

/-- The literal local lift on its actual source open set. -/
def liftOn (P : HolomorphicPeriodMap V B) (i : B × ComplexPlane₂) :
    coverOpen P i → B × ComplexPlane₂ := fun x => lift P i x

@[simp] theorem liftOn_apply (P : HolomorphicPeriodMap V B) (i : B × ComplexPlane₂)
    (x : coverOpen P i) : liftOn P i x = lift P i x := rfl

theorem project_liftOn (P : HolomorphicPeriodMap V B) (i : B × ComplexPlane₂)
    (x : coverOpen P i) : P.quotientMap (liftOn P i x) = x := project_lift P i x.property

variable [IsManifold (modelWithCornersSelf ℂ V) ω B]

/-- The original product atlas upstairs is holomorphic. -/
theorem cover_isManifold :
    letI := coverChartedSpace (V := V) (B := B)
    IsManifold IT ω (B × ComplexPlane₂) := by
  let := coverChartedSpace (V := V) (B := B)
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := IB) (I' := modelWithCornersSelf ℂ ComplexPlane₂) B ComplexPlane₂

/-- Every original quotient-cover local inverse is holomorphic on its own source. -/
theorem lift_holomorphic (P : HolomorphicPeriodMap V B) (i : B × ComplexPlane₂) :
    letI := coverChartedSpace (V := V) (B := B)
    letI := P.totalChartedSpace
    ContMDiffOn IT IT ω (lift P i) (coverOpen P i) := by
  let := coverChartedSpace (V := V) (B := B)
  let := P.totalChartedSpace
  let := P.coveringAction
  let : IsManifold IT ω (B × ComplexPlane₂) := cover_isManifold
  exact CoveringQuotient.localInverse_holomorphic P.quotientCoveringMap ω
    P.coveringAction_holomorphic i

/-- The bundled-domain local lift is genuinely holomorphic in those same unchanged atlases. -/
theorem liftOn_holomorphic (P : HolomorphicPeriodMap V B) (i : B × ComplexPlane₂) :
    letI := coverChartedSpace (V := V) (B := B)
    letI := P.totalChartedSpace
    ContMDiff IT IT ω (liftOn P i) := by
  let := coverChartedSpace (V := V) (B := B)
  let := P.totalChartedSpace
  intro x
  exact ((lift_holomorphic P i).contMDiffAt
    ((coverOpen P i).isOpen.mem_nhds x.property)).comp x (contMDiff_subtype_val x)

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.Cocycle
