import Wikipedia.HopfProblem.CuspComponentImmersion
import Wikipedia.HopfProblem.CuspRationalCurves
import Wikipedia.HopfProblem.AffineSphereImmersion

/-!
# The double curves are embedded holomorphic spheres

The affine axis lifts have the exact coordinate-inclusion normal form.
This persists through the holomorphic covering quotient and verifies the
ambient immersion property on both affine charts of each double curve.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspQuotient

open ToricCharts ToricSpace ToricFan Triangle ToricComponent

def axisJoin (j : Fin 3) : (ℂ × CoordinateSpace 2) ≃L[ℂ] CoordinateSpace 3 :=
  (ContinuousLinearEquiv.prodComm ℂ ℂ (CoordinateSpace 2)).trans (coordinateJoin j)

theorem axisJoin_apply_zero (s : Triangle) (i : Fin 3) (z : ℂ) :
    axisJoin (s.axisIndex i) (z, 0) = axisPoint s i z := by
  change Fin.insertNth (s.axisIndex i) z (0 : CoordinateSpace 2) = axisPoint s i z
  apply Fin.insertNth_eq_iff.mpr
  constructor
  · exact (axisPoint_apply_axisIndex s i z).symm
  · ext j
    exact (axisPoint_apply_of_ne s i ((s.axisIndex i).succAbove j) z
      (Fin.succAbove_ne _ _)).symm

variable (ε : ℝ) (hε : 0 < ε)

theorem axisLift_isImmersionOfComplement (s : Triangle) (i : Fin 3) :
    Manifold.IsImmersionOfComplement (CoordinateSpace 2) (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω (axisLift ε hε s i) := by
  intro z
  let e := (ToricSpace.parametrization s).symm
  let hU : Nonempty (tubeOpen (disc ε)) := ⟨axisLift ε hε s i z⟩
  have he : e ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω Space :=
    IsManifold.subset_maximalAtlas (mem_range_self s)
  refine Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
    (axisLift_continuous ε hε s i).continuousAt (axisJoin (s.axisIndex i))
    (OpenPartialHomeomorph.refl ℂ) (e.subtypeRestr hU) (mem_univ z) ?_ ?_ ?_ ?_
  · rw [e.subtypeRestr_source]
    change inclusion s (axisPoint s i z) ∈ (ToricSpace.parametrization s).target
    rw [ToricSpace.parametrization_target]
    exact mem_range_self _
  · simpa only [chartAt_self_eq] using IsManifold.chart_mem_maximalAtlas
      (I := modelWithCornersSelf ℂ ℂ) (n := ω) z
  · exact normalCrossing_subtype_chart (tubeOpen (disc ε)) hU e he
  · intro w _
    change (ToricSpace.parametrization s).symm (inclusion s (axisPoint s i w)) =
      axisJoin (s.axisIndex i) (w, 0)
    rw [axisJoin_apply_zero]
    exact (ToricSpace.parametrization s).left_inv (mem_univ _)

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

theorem axisMap_isImmersionOfComplement (s : Triangle) (i : Fin 3) :
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    Manifold.IsImmersionOfComplement (CoordinateSpace 2) (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω (axisMap C ε hε s i) := by
  let := tubeAction C (disc ε)
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  exact CoveringQuotient.immersion_project (quotientMap_covering C ε hε hε1 hC hR)
    (fun g => tubeTranslate_holomorphic C (disc ε) g.toAdd hC)
    (axisLift_continuous ε hε s i) (axisLift_isImmersionOfComplement ε hε s i)

theorem curve_inclusion_isImmersionOfComplement (i : Fin 3) :
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    letI := curveChartedSpace C ε hε hε1 hC hR i
    Manifold.IsImmersionOfComplement (CoordinateSpace 2) (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω
      (Subtype.val : doubleCurve C ε hε i → QuotientSpace C ε) := by
  let := quotient_t2Space C ε hε hε1 hC hR
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  let := curveChartedSpace C ε hε hε1 hC hR i
  apply (curveCharts C ε hε i).immersion_of_comp_affineMaps _ continuous_subtype_val
  intro b
  cases b
  · exact axisMap_isImmersionOfComplement ε hε C hε1 hC hR referenceTriangle i
  · exact axisMap_isImmersionOfComplement ε hε C hε1 hC hR (upperNeighbour i) i

theorem curve_inclusion_isImmersion (i : Fin 3) :
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    letI := curveChartedSpace C ε hε hε1 hC hR i
    Manifold.IsImmersion (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω
      (Subtype.val : doubleCurve C ε hε i → QuotientSpace C ε) := by
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  let := curveChartedSpace C ε hε hε1 hC hR i
  exact (curve_inclusion_isImmersionOfComplement ε hε C hε1 hC hR i).isImmersion

theorem sphereParametrization_isImmersion (i : Fin 3) :
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    Manifold.IsImmersion (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω
      (sphereParametrization C ε hε hε1 hC hR i) := by
  let := quotient_t2Space C ε hε hε1 hC hR
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  apply Manifold.IsImmersionOfComplement.isImmersion (F := CoordinateSpace 2)
  apply RiemannSphere.standardCharts.immersion_of_comp_affineMaps _
    (sphereParametrization_holomorphic C ε hε hε1 hC hR i).continuous
  intro b
  change Manifold.IsImmersionOfComplement (CoordinateSpace 2) (modelWithCornersSelf ℂ ℂ)
    (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω
    ((Subtype.val ∘ (curveCharts C ε hε i).homeomorph) ∘
      RiemannSphere.standardCharts.affineMap b)
  rw [Function.comp_assoc, RiemannSphere.homeomorph_comp_standardCharts]
  cases b
  · exact axisMap_isImmersionOfComplement ε hε C hε1 hC hR referenceTriangle i
  · exact axisMap_isImmersionOfComplement ε hε C hε1 hC hR (upperNeighbour i) i

end Wikipedia.HopfProblem.CuspQuotient
