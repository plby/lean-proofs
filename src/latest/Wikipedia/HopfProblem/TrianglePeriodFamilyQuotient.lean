import Wikipedia.HopfProblem.TrianglePeriodFamilyAction
import Wikipedia.HopfProblem.TrianglePeriodFamilyTopology
import Wikipedia.HopfProblem.CoveringSubmersion

/-!
# The actual analytic quotient of a triangle-equivariant period family

The base and total-space orbit quotients carry their inherited quotient
topologies.  Their analytic atlases are explicitly selected from the
given base and period-family atlases.  The actual descended family
projection is proper, surjective, holomorphic, and a submersion.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Data

open SpecialPeriods

variable {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [MulAction TriangleGroup B]

/-- A parameterized type for the actual base orbit quotient. -/
def BaseSpace (_D : TrianglePeriodFamily.Data V B) : Type _ :=
  DiagonalQuotient.BaseSpace TriangleGroup B

/-- A fresh type for the actual diagonal orbit quotient of this period
family, with no globally installed analytic structure. -/
def Space (D : TrianglePeriodFamily.Data V B) : Type _ :=
  @MulAction.orbitRel.Quotient TriangleGroup D.TotalSpace _ D.totalAction

variable (D : TrianglePeriodFamily.Data V B)

instance baseSpaceTopology : TopologicalSpace D.BaseSpace :=
  inferInstanceAs (TopologicalSpace (DiagonalQuotient.BaseSpace TriangleGroup B))

instance spaceTopology : TopologicalSpace D.Space :=
  inferInstanceAs (TopologicalSpace
    (@MulAction.orbitRel.Quotient TriangleGroup D.TotalSpace _ D.totalAction))

/-- The actual base quotient map. -/
def baseQuotient : B → D.BaseSpace := DiagonalQuotient.baseQuotient TriangleGroup B

/-- The actual total-space quotient map. -/
def quotient : D.TotalSpace → D.Space := by
  let := triangleTorusAction
  exact DiagonalQuotient.quotient TriangleGroup B RealTorus₄

/-- The actual map between the two orbit quotients induced by the
varying-period family's base projection. -/
def projection : D.Space → D.BaseSpace := by
  let := triangleTorusAction
  exact DiagonalQuotient.projection TriangleGroup B RealTorus₄

@[simp] theorem projection_quotient (x : D.TotalSpace) :
    D.projection (D.quotient x) = D.baseQuotient (D.periods.projection x) := rfl

theorem baseQuotient_surjective : Function.Surjective D.baseQuotient :=
  DiagonalQuotient.baseQuotient_surjective TriangleGroup B

theorem quotient_surjective : Function.Surjective D.quotient := by
  let := triangleTorusAction
  exact DiagonalQuotient.quotient_surjective TriangleGroup B RealTorus₄

theorem projection_surjective : Function.Surjective D.projection := by
  let := triangleTorusAction
  exact DiagonalQuotient.projection_surjective TriangleGroup B RealTorus₄

theorem baseQuotient_continuous : Continuous D.baseQuotient :=
  DiagonalQuotient.baseQuotient_continuous TriangleGroup B

theorem quotient_continuous : Continuous D.quotient := by
  let := triangleTorusAction
  exact DiagonalQuotient.quotient_continuous TriangleGroup B RealTorus₄

theorem projection_continuous : Continuous D.projection := by
  let := triangleTorusAction
  exact DiagonalQuotient.projection_continuous TriangleGroup B RealTorus₄

theorem quotient_isQuotientMap : IsQuotientMap D.quotient := by
  let := triangleTorusAction
  exact DiagonalQuotient.quotient_isQuotientMap TriangleGroup B RealTorus₄

theorem quotient_eq_iff (x y : D.TotalSpace) :
    letI := D.totalAction
    D.quotient x = D.quotient y ↔ ∃ g : TriangleGroup, g • y = x := by
  let := triangleTorusAction
  exact DiagonalQuotient.quotient_eq_iff TriangleGroup B RealTorus₄ x y

@[simp] theorem quotient_smul (g : TriangleGroup) (x : D.TotalSpace) :
    letI := D.totalAction
    D.quotient (g • x) = D.quotient x := by
  let := triangleTorusAction
  exact DiagonalQuotient.quotient_smul TriangleGroup B RealTorus₄ g x

variable (hq : IsQuotientCoveringMap D.baseQuotient TriangleGroup)

include hq

/-- Base freeness and local disjoint sheets give a genuine covering on
the entire actual period family. -/
theorem quotientCoveringMap :
    letI := D.totalAction
    IsQuotientCoveringMap D.quotient TriangleGroup := by
  let := triangleTorusAction
  let := triangleTorusAction_continuous
  exact DiagonalQuotient.quotientCoveringMap (F := RealTorus₄) hq

theorem quotient_isCoveringMap : IsCoveringMap D.quotient := by
  let := D.totalAction
  exact (D.quotientCoveringMap hq).isCoveringMap

theorem quotient_isOpenQuotientMap : IsOpenQuotientMap D.quotient := by
  let := triangleTorusAction
  let := triangleTorusAction_continuous
  exact DiagonalQuotient.quotient_isOpenQuotientMap (F := RealTorus₄) hq

/-- The compact real torus fibres and the constructed local products
prove properness of this actual descended projection. -/
theorem projection_proper : IsProperMap D.projection := by
  let := triangleTorusAction
  let := triangleTorusAction_continuous
  exact DiagonalQuotient.projection_proper (F := RealTorus₄) hq

theorem baseT2Space [T2Space B] [LocallyCompactSpace B]
    [ProperlyDiscontinuousSMul TriangleGroup B] : T2Space D.BaseSpace :=
  DiagonalQuotient.baseT2Space hq

theorem spaceT2Space [T2Space D.BaseSpace] : T2Space D.Space := by
  let := triangleTorusAction
  let := triangleTorusAction_continuous
  let : T2Space (DiagonalQuotient.BaseSpace TriangleGroup B) := ‹T2Space D.BaseSpace›
  exact DiagonalQuotient.spaceT2Space (F := RealTorus₄) hq

theorem spaceT2Space_of_properlyDiscontinuous [T2Space B] [LocallyCompactSpace B]
    [ProperlyDiscontinuousSMul TriangleGroup B] : T2Space D.Space := by
  let := D.baseT2Space hq
  exact D.spaceT2Space hq

theorem baseSecondCountable [SecondCountableTopology B] :
    SecondCountableTopology D.BaseSpace :=
  hq.toIsQuotientMap.secondCountableTopology hq.isCoveringMap.isLocalHomeomorph.isOpenMap

theorem spaceSecondCountable [SecondCountableTopology B] :
    SecondCountableTopology D.Space := by
  let := triangleTorusAction
  let := triangleTorusAction_continuous
  exact DiagonalQuotient.spaceSecondCountable (F := RealTorus₄) hq

theorem baseLocallyCompact [LocallyCompactSpace B] : LocallyCompactSpace D.BaseSpace := by
  have hopen : IsOpenQuotientMap D.baseQuotient :=
    ⟨hq.surjective, hq.continuous, hq.isCoveringMap.isLocalHomeomorph.isOpenMap⟩
  exact hopen.locallyCompactSpace

theorem spaceLocallyCompact [LocallyCompactSpace B] : LocallyCompactSpace D.Space := by
  let := triangleTorusAction
  let := triangleTorusAction_continuous
  exact DiagonalQuotient.spaceLocallyCompact (F := RealTorus₄) hq

/-- The base quotient atlas lifted through its actual covering map. -/
@[instance_reducible] def baseChartedSpace : ChartedSpace V D.BaseSpace :=
  CoveringQuotient.chartedSpace (E := V) hq

/-- The total quotient atlas lifted from this supplied varying-period
family, not from its underlying real product. -/
@[instance_reducible] def chartedSpace : ChartedSpace (V × ComplexPlane₂) D.Space := by
  let := D.periods.totalChartedSpace
  let := D.totalAction
  exact CoveringQuotient.chartedSpace (E := V × ComplexPlane₂) (D.quotientCoveringMap hq)

variable [IsManifold (modelWithCornersSelf ℂ V) ω B]

/-- The actual base quotient is a complex manifold for its selected atlas. -/
theorem baseIsManifold :
    letI := D.baseChartedSpace hq
    IsManifold (modelWithCornersSelf ℂ V) ω D.BaseSpace :=
  CoveringQuotient.isManifold hq ω D.base_holomorphic

/-- The actual total quotient is a complex manifold for the selected
atlas coming from the supplied holomorphic periods. -/
theorem isManifold :
    letI := D.chartedSpace hq
    IsManifold (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω D.Space := by
  let := D.periods.totalChartedSpace
  let := D.periods.totalSpace_isManifold
  let := D.totalAction
  exact CoveringQuotient.isManifold (D.quotientCoveringMap hq) ω D.totalAction_holomorphic

theorem baseQuotient_holomorphic :
    letI := D.baseChartedSpace hq
    ContMDiff (modelWithCornersSelf ℂ V) (modelWithCornersSelf ℂ V) ω D.baseQuotient :=
  CoveringQuotient.contMDiff_project hq ω D.base_holomorphic

theorem quotient_holomorphic :
    letI := D.periods.totalChartedSpace
    letI := D.chartedSpace hq
    ContMDiff (modelWithCornersSelf ℂ (V × ComplexPlane₂))
      (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω D.quotient := by
  let := D.periods.totalChartedSpace
  let := D.periods.totalSpace_isManifold
  let := D.totalAction
  exact CoveringQuotient.contMDiff_project (D.quotientCoveringMap hq) ω
    D.totalAction_holomorphic

theorem projection_holomorphic :
    letI := D.baseChartedSpace hq
    letI := D.chartedSpace hq
    ContMDiff (modelWithCornersSelf ℂ (V × ComplexPlane₂)) (modelWithCornersSelf ℂ V) ω
      D.projection := by
  let := D.periods.totalChartedSpace
  let := D.periods.totalSpace_isManifold
  let := D.baseChartedSpace hq
  let := D.totalAction
  apply CoveringQuotient.contMDiff_of_comp (D.quotientCoveringMap hq)
    (modelWithCornersSelf ℂ V) ω
  exact (D.baseQuotient_holomorphic hq).comp D.periods.projection_holomorphic

/-- The full holomorphic submersion normal form descends through the
commuting square of the two actual covering quotients. -/
theorem projection_submersion :
    letI := D.baseChartedSpace hq
    letI := D.chartedSpace hq
    Manifold.IsSubmersionOfComplement ComplexPlane₂
      (modelWithCornersSelf ℂ (V × ComplexPlane₂)) (modelWithCornersSelf ℂ V) ω
      D.projection := by
  let := D.periods.totalChartedSpace
  let := D.periods.totalSpace_isManifold
  let := D.totalAction
  exact CoveringQuotient.submersion_descend (D.quotientCoveringMap hq) hq
    D.totalAction_holomorphic D.base_holomorphic D.periods.projection_submersion
    (D.projection_quotient)

end Wikipedia.HopfProblem.TrianglePeriodFamily.Data
