import Wikipedia.HopfProblem.ToricComponentCharts
import Wikipedia.HopfProblem.CuspComponentProper

/-!
# The compact complex ray surfaces and their holomorphic projection

The coordinate-hyperplane charts give the actual ray components compatible
complex two-manifold structures. Their subspace topology is unchanged, and
their inclusions into the toric threefold are holomorphic. The component
projection to the cusp quotient is consequently holomorphic as well as
proper with finite fibres. No del Pezzo identification is assumed.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.ToricComponent

open ToricCharts ToricFan ToricSpace

@[simp] theorem affineInclusion_coe {v : Fin 2 → ℤ} (c : ChartIndex v) (z : CoordinateSpace 2) :
    (affineInclusion c z : Space) = inclusion c.triangle (insertZero c.coordinate z) := rfl

def preferredIndex (v : Fin 2 → ℤ) (x : rayDivisor v) : ChartIndex v :=
  (affineInclusion_jointly_surjective x).choose

theorem preferred_mem (v : Fin 2 → ℤ) (x : rayDivisor v) :
    x ∈ range (affineInclusion (preferredIndex v x)) :=
  (affineInclusion_jointly_surjective x).choose_spec

instance chartedSpace (v : Fin 2 → ℤ) : ChartedSpace (CoordinateSpace 2) (rayDivisor v) where
  atlas := range (fun c : ChartIndex v => (parametrization c).symm)
  chartAt x := (parametrization (preferredIndex v x)).symm
  mem_chart_source x := by
    change x ∈ (parametrization (preferredIndex v x)).target
    rw [parametrization_target]
    exact preferred_mem v x
  chart_mem_atlas _ := mem_range_self _

instance isManifold (v : Fin 2 → ℤ) :
    IsManifold (modelWithCornersSelf ℂ (CoordinateSpace 2)) ω (rayDivisor v) := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨c, rfl⟩ := he
  obtain ⟨d, rfl⟩ := he'
  simpa using transition_holomorphic c d

theorem affineInclusion_holomorphic {v : Fin 2 → ℤ} (c : ChartIndex v) :
    ContMDiff (modelWithCornersSelf ℂ (CoordinateSpace 2))
      (modelWithCornersSelf ℂ (CoordinateSpace 2)) ω (affineInclusion c) := by
  have he : (parametrization c).symm ∈ IsManifold.maximalAtlas
      (modelWithCornersSelf ℂ (CoordinateSpace 2)) ω (rayDivisor v) :=
    IsManifold.subset_maximalAtlas (mem_range_self c)
  have h := contMDiffOn_symm_of_mem_maximalAtlas he
  change ContMDiffOn (modelWithCornersSelf ℂ (CoordinateSpace 2))
    (modelWithCornersSelf ℂ (CoordinateSpace 2)) ω (affineInclusion c) univ at h
  exact contMDiffOn_univ.mp h

theorem contMDiff_of_comp_affineInclusions {F H N : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [TopologicalSpace H] [TopologicalSpace N] [ChartedSpace H N]
    (v : Fin 2 → ℤ) (I : ModelWithCorners ℂ F H) (f : rayDivisor v → N)
    (hf : ∀ c : ChartIndex v, ContMDiff (modelWithCornersSelf ℂ (CoordinateSpace 2))
      I ω (f ∘ affineInclusion c)) :
    ContMDiff (modelWithCornersSelf ℂ (CoordinateSpace 2)) I ω f := by
  intro x
  rw [contMDiffAt_iff_source]
  have hchart : chartAt (CoordinateSpace 2) x = (parametrization (preferredIndex v x)).symm := rfl
  simpa [extChartAt, OpenPartialHomeomorph.extend, hchart, Function.comp_def] using
    (hf (preferredIndex v x)).contMDiffAt.contMDiffWithinAt
      (s := univ) (x := (parametrization (preferredIndex v x)).symm x)

theorem inclusion_holomorphic (v : Fin 2 → ℤ) :
    ContMDiff (modelWithCornersSelf ℂ (CoordinateSpace 2))
      (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω (Subtype.val : rayDivisor v → Space) := by
  apply contMDiff_of_comp_affineInclusions v (modelWithCornersSelf ℂ (CoordinateSpace 3))
  intro c
  exact (ToricSpace.inclusion_holomorphic c.triangle).comp
    (insertZero_holomorphic c.coordinate).contMDiff

end Wikipedia.HopfProblem.ToricComponent

namespace Wikipedia.HopfProblem.CuspQuotient

open ToricCharts ToricSpace

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)

theorem componentLift_holomorphic :
    ContMDiff (modelWithCornersSelf ℂ (CoordinateSpace 2))
      (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω (componentLift ε hε) := by
  intro x
  have he : ContMDiffAt (modelWithCornersSelf ℂ (CoordinateSpace 2))
      (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω
      (fun y => (componentLift ε hε y : Space)) x ↔
    ContMDiffAt (modelWithCornersSelf ℂ (CoordinateSpace 2))
      (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω (componentLift ε hε) x :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp (ToricComponent.inclusion_holomorphic 0 x)

theorem componentProjection_holomorphic (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε) :
    letI := chartedSpace C ε hε hε1 hC hR
    ContMDiff (modelWithCornersSelf ℂ (CoordinateSpace 2))
      (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω (componentProjection C ε hε) := by
  let := chartedSpace C ε hε hε1 hC hR
  exact (quotientMap_holomorphic C ε hε hε1 hC hR).comp (componentLift_holomorphic ε hε)

end Wikipedia.HopfProblem.CuspQuotient
