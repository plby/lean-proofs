import Wikipedia.HopfProblem.CuspExponentials

/-!
# An analytic chart on the dense torus

The chart-independent characters form a genuine open partial homeomorphism
onto `(ℂ*)³`. Its third coordinate is the cusp parameter. Restricting this
chart to an open tube preserves both analytic directions.
-/

noncomputable section

open Set Topology
open scoped ContDiff Matrix

namespace Wikipedia.HopfProblem.CuspUniformization

open ToricCharts ToricFan ToricSpace

theorem torusPoint_holomorphic :
    ContMDiffOn (modelWithCornersSelf ℂ (CoordinateSpace 3))
      (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω torusPoint torus :=
  (inclusion_holomorphic referenceTriangle).comp_contMDiffOn
    ((monomial_contDiffOn referenceTriangle.dual ω).mono (torus_subset_domain _)).contMDiffOn

def torusChart : OpenPartialHomeomorph Space (CoordinateSpace 3) where
  toFun := torusCoordinates
  invFun := torusPoint
  source := openTorus
  target := torus
  map_source' _ hx := torusCoordinates_nonzero hx
  map_target' _ hw := torusPoint_mem hw
  left_inv' _ hx := torusPoint_torusCoordinates hx
  right_inv' _ hw := torusCoordinates_torusPoint hw
  open_source := openTorus_isOpen
  open_target := torus_open
  continuousOn_toFun := torusCoordinates_holomorphic.continuousOn
  continuousOn_invFun := torusPoint_holomorphic.continuousOn

theorem torusChart_mem_maximalAtlas :
    torusChart ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω Space :=
  torusChart.mem_maximalAtlas_of_contMDiffOn
    torusCoordinates_holomorphic torusPoint_holomorphic

theorem torusChart_symm_time {w : CoordinateSpace 3} (hw : w ∈ torusChart.target) :
    time (torusChart.symm w) = w 2 := by
  have he := congrFun (torusChart.right_inv hw) 2
  change torusCoordinates (torusChart.symm w) 2 = w 2 at he
  rwa [torusCoordinates_time] at he

variable (D : TopologicalSpace.Opens ℂ) (hD : Nonempty (Tube D))

def tubeTorusChart : OpenPartialHomeomorph (Tube D) (CoordinateSpace 3) :=
  torusChart.subtypeRestr hD

@[simp] theorem tubeTorusChart_source :
    (tubeTorusChart D hD).source = Subtype.val ⁻¹' openTorus :=
  torusChart.subtypeRestr_source hD

theorem tubeTorusChart_holomorphic :
    ContMDiffOn (modelWithCornersSelf ℂ (CoordinateSpace 3))
      (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω (tubeTorusChart D hD)
      (tubeTorusChart D hD).source := by
  rw [tubeTorusChart_source]
  have hval : ContMDiff (modelWithCornersSelf ℂ (CoordinateSpace 3))
      (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω (Subtype.val : Tube D → Space) :=
    contMDiff_subtype_val
  exact torusCoordinates_holomorphic.comp hval.contMDiffOn (fun _ hx => hx)

theorem tubeTorusChart_symm_holomorphic :
    ContMDiffOn (modelWithCornersSelf ℂ (CoordinateSpace 3))
      (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω (tubeTorusChart D hD).symm
      (tubeTorusChart D hD).target := by
  have hv : ContMDiffOn (modelWithCornersSelf ℂ (CoordinateSpace 3))
      (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω
      (Subtype.val ∘ (tubeTorusChart D hD).symm) (tubeTorusChart D hD).target :=
    (torusPoint_holomorphic.mono (torusChart.subtypeRestr_target_subset hD)).congr
      (fun _ hw => torusChart.subtypeRestr_symm_apply hD hw)
  intro w hw
  have he : ContMDiffWithinAt (modelWithCornersSelf ℂ (CoordinateSpace 3))
      (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω
      (Subtype.val ∘ (tubeTorusChart D hD).symm) (tubeTorusChart D hD).target w ↔
    ContMDiffWithinAt (modelWithCornersSelf ℂ (CoordinateSpace 3))
      (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω
      (tubeTorusChart D hD).symm (tubeTorusChart D hD).target w :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp (hv w hw)

theorem tubeTorusChart_mem_maximalAtlas :
    tubeTorusChart D hD ∈ IsManifold.maximalAtlas
      (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω (Tube D) :=
  (tubeTorusChart D hD).mem_maximalAtlas_of_contMDiffOn
    (tubeTorusChart_holomorphic D hD) (tubeTorusChart_symm_holomorphic D hD)

theorem tubeTorusChart_symm_time {w : CoordinateSpace 3}
    (hw : w ∈ (tubeTorusChart D hD).target) :
    time ((tubeTorusChart D hD).symm w : Space) = w 2 := by
  rw [show ((tubeTorusChart D hD).symm w : Space) = torusChart.symm w from
    torusChart.subtypeRestr_symm_apply hD hw]
  exact torusChart_symm_time (torusChart.subtypeRestr_target_subset hD hw)

end Wikipedia.HopfProblem.CuspUniformization
