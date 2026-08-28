import Wikipedia.HopfProblem.PeriodFamily
import Wikipedia.HopfProblem.CoveringImmersion
import Wikipedia.HopfProblem.CuspFibreImmersion

/-!
# The period-family fibres are immersed complex tori

Fixing a base point gives a coordinate-plane inclusion in the covering
product. Its immersion normal form descends first through the varying-period
covering and then through the fixed fibre lattice quotient.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.HolomorphicPeriodMap

variable {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B]

local instance (priority := 100) fibreProductChartedSpace :
    ChartedSpace (V × ComplexPlane₂) (B × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd V ComplexPlane₂) (B × ComplexPlane₂))

local instance (priority := 100) fibreProductManifold
    [IsManifold (modelWithCornersSelf ℂ V) ω B] :
    IsManifold (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω (B × ComplexPlane₂) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := modelWithCornersSelf ℂ V)
    (I' := modelWithCornersSelf ℂ ComplexPlane₂) B ComplexPlane₂

private def fibreBaseShift (b : B) : (V × ComplexPlane₂) ≃ₜ (V × ComplexPlane₂) :=
  Homeomorph.addRight (-((chartAt V b) b, (0 : ComplexPlane₂)))

private theorem fibreBaseShift_holomorphic (b : B) :
    ContMDiff (modelWithCornersSelf ℂ (V × ComplexPlane₂))
      (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω (fibreBaseShift (V := V) b) :=
  (contDiff_id.add contDiff_const).contMDiff

private theorem fibreBaseShift_symm_holomorphic (b : B) :
    ContMDiff (modelWithCornersSelf ℂ (V × ComplexPlane₂))
      (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω (fibreBaseShift (V := V) b).symm := by
  rw [fibreBaseShift, Homeomorph.addRight_symm]
  exact (contDiff_id.add contDiff_const).contMDiff

private def fixedBaseChart (b : B) :
    OpenPartialHomeomorph (B × ComplexPlane₂) (V × ComplexPlane₂) :=
  (chartAt (V × ComplexPlane₂) (b, (0 : ComplexPlane₂))).trans
    (fibreBaseShift (V := V) b).toOpenPartialHomeomorph

variable [IsManifold (modelWithCornersSelf ℂ V) ω B]

private theorem fixedBaseChart_mem_maximalAtlas (b : B) :
    fixedBaseChart (V := V) b ∈ IsManifold.maximalAtlas
      (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω (B × ComplexPlane₂) := by
  have hc := IsManifold.chart_mem_maximalAtlas
    (I := modelWithCornersSelf ℂ (V × ComplexPlane₂)) (n := ω) (b, (0 : ComplexPlane₂))
  apply (fixedBaseChart (V := V) b).mem_maximalAtlas_of_contMDiffOn
  · exact (fibreBaseShift_holomorphic (V := V) b).comp_contMDiffOn
      ((contMDiffOn_of_mem_maximalAtlas hc).mono inter_subset_left)
  · exact (contMDiffOn_symm_of_mem_maximalAtlas hc).comp
      ((fibreBaseShift_symm_holomorphic (V := V) b).contMDiffOn.mono inter_subset_left)
      (fun _ hw => hw.2)

theorem fixedBase_isImmersionOfComplement (b : B) :
    Manifold.IsImmersionOfComplement V (modelWithCornersSelf ℂ ComplexPlane₂)
      (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω
      (fun z : ComplexPlane₂ => (b, z)) := by
  intro z
  refine Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
    (continuous_const.prodMk continuous_id).continuousAt
    (ContinuousLinearEquiv.prodComm ℂ ComplexPlane₂ V)
    (OpenPartialHomeomorph.refl ComplexPlane₂) (fixedBaseChart b)
    (mem_univ _) ?_ ?_ (fixedBaseChart_mem_maximalAtlas b) ?_
  · refine ⟨?_, mem_univ _⟩
    exact ⟨mem_chart_source V b, mem_univ z⟩
  · exact IsManifold.chart_mem_maximalAtlas z
  · intro w _
    change ((chartAt V b) b, w) + -((chartAt V b) b, (0 : ComplexPlane₂)) = (0, w)
    simp

theorem fibreInclusion_isImmersionOfComplement (P : HolomorphicPeriodMap V B) (b : B) :
    letI := P.totalChartedSpace
    Manifold.IsImmersionOfComplement V (modelWithCornersSelf ℂ ComplexPlane₂)
      (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω (P.fibreInclusion b) := by
  let := P.totalChartedSpace
  let := P.coveringAction
  apply DiscreteQuotient.immersion_of_comp_mkQ (P.point b).lattice
    (P.fibreInclusion_holomorphic b).continuous
  change Manifold.IsImmersionOfComplement V (modelWithCornersSelf ℂ ComplexPlane₂)
    (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω
    (P.quotientMap ∘ (fun z : ComplexPlane₂ => (b, z)))
  exact CoveringQuotient.immersion_project (E := V × ComplexPlane₂)
    P.quotientCoveringMap P.coveringAction_holomorphic
    (continuous_const.prodMk continuous_id) (fixedBase_isImmersionOfComplement b)

theorem fibreInclusion_isImmersion (P : HolomorphicPeriodMap V B) (b : B) :
    letI := P.totalChartedSpace
    Manifold.IsImmersion (modelWithCornersSelf ℂ ComplexPlane₂)
      (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω (P.fibreInclusion b) := by
  let := P.totalChartedSpace
  exact (P.fibreInclusion_isImmersionOfComplement b).isImmersion

end Wikipedia.HopfProblem.HolomorphicPeriodMap
