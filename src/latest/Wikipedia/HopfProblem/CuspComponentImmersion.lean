import Wikipedia.HopfProblem.ToricComponentImmersion
import Wikipedia.HopfProblem.CoveringImmersion
import Wikipedia.HopfProblem.NormalCrossing

/-!
# The component projection is a holomorphic immersion

The inclusion of `E₀` in the open tube has the coordinate-hyperplane normal
form. The quotient is locally biholomorphic, so the actual component
projection retains this normal form even over the double and triple points.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspQuotient

open ToricCharts ToricSpace ToricComponent

variable (ε : ℝ) (hε : 0 < ε)

theorem componentLift_isImmersionOfComplement :
    Manifold.IsImmersionOfComplement ℂ (modelWithCornersSelf ℂ (CoordinateSpace 2))
      (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω (componentLift ε hε) := by
  intro x
  let c := ToricComponent.preferredIndex 0 x
  let e := (ToricSpace.parametrization c.triangle).symm
  let hU : Nonempty (tubeOpen (disc ε)) := ⟨componentLift ε hε x⟩
  have he : e ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω Space :=
    IsManifold.subset_maximalAtlas (mem_range_self c.triangle)
  refine Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
    (componentLift_holomorphic ε hε).continuous.continuousAt (coordinateJoin c.coordinate)
    (ToricComponent.parametrization c).symm (e.subtypeRestr hU) ?_ ?_ ?_ ?_ ?_
  · change x ∈ (ToricComponent.parametrization c).target
    rw [ToricComponent.parametrization_target]
    exact ToricComponent.preferred_mem 0 x
  · rw [e.subtypeRestr_source]
    change (x : Space) ∈ (ToricSpace.parametrization c.triangle).target
    rw [ToricSpace.parametrization_target]
    exact (affineInclusion_mem_range_iff c x).mp (ToricComponent.preferred_mem 0 x)
  · exact IsManifold.subset_maximalAtlas (mem_range_self c)
  · exact normalCrossing_subtype_chart (tubeOpen (disc ε)) hU e he
  · intro z _
    change (ToricSpace.parametrization c.triangle).symm
      (inclusion c.triangle (insertZero c.coordinate z)) = insertZero c.coordinate z
    exact (ToricSpace.parametrization c.triangle).left_inv (mem_univ _)

theorem componentProjection_isImmersionOfComplement
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε) :
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    Manifold.IsImmersionOfComplement ℂ (modelWithCornersSelf ℂ (CoordinateSpace 2))
      (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω (componentProjection C ε hε) := by
  let := tubeAction C (disc ε)
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  exact CoveringQuotient.immersion_project (quotientMap_covering C ε hε hε1 hC hR)
    (fun g => tubeTranslate_holomorphic C (disc ε) g.toAdd hC)
    (componentLift_holomorphic ε hε).continuous (componentLift_isImmersionOfComplement ε hε)

theorem componentProjection_isImmersion
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε) :
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    Manifold.IsImmersion (modelWithCornersSelf ℂ (CoordinateSpace 2))
      (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω (componentProjection C ε hε) := by
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  exact (componentProjection_isImmersionOfComplement ε hε C hε1 hC hR).isImmersion

end Wikipedia.HopfProblem.CuspQuotient
