import Wikipedia.HopfProblem.CuspNormalizationSheafCurvesLifts

/-!
# Holomorphicity of the two boundary lifts

The inverse boundary projections are holomorphic for the already constructed
analytic atlas of each actual double curve. Their affine expressions are the
translated coordinate axes, so no analytic inverse theorem is assumed.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspQuotient.NormalizationCurves

open ToricCharts ToricFan ToricSpace ToricComponent Triangle

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

theorem plusLift_holomorphic (i : Fin 3) :
    letI := curveChartedSpace C ε hε hε1 hC hR i
    ContMDiff (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ (CoordinateSpace 2)) ω (plusLift C ε hε i) := by
  let := quotient_t2Space C ε hε hε1 hC hR
  let := curveChartedSpace C ε hε hε1 hC hR i
  apply (curveCharts C ε hε i).contMDiff_of_comp_affineMaps
    (modelWithCornersSelf ℂ (CoordinateSpace 2))
  intro b
  cases b
  · change ContMDiff _ _ _ (fun z => plusLift C ε hε i
      ⟨axisMap C ε hε referenceTriangle i z, _⟩)
    simpa only [plusLift_axisMap] using
      affineLift_holomorphic C referenceTriangle i (referenceTriangle.edgeStart i)
  · change ContMDiff _ _ _ (fun z => plusLift C ε hε i
      ⟨axisMap C ε hε (upperNeighbour i) i z, _⟩)
    simpa only [plusLift_axisMap] using
      affineLift_holomorphic C (upperNeighbour i) i ((upperNeighbour i).edgeStart i)

theorem minusLift_holomorphic (i : Fin 3) :
    letI := curveChartedSpace C ε hε hε1 hC hR i
    ContMDiff (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ (CoordinateSpace 2)) ω (minusLift C ε hε i) := by
  let := quotient_t2Space C ε hε hε1 hC hR
  let := curveChartedSpace C ε hε hε1 hC hR i
  apply (curveCharts C ε hε i).contMDiff_of_comp_affineMaps
    (modelWithCornersSelf ℂ (CoordinateSpace 2))
  intro b
  cases b
  · change ContMDiff _ _ _ (fun z => minusLift C ε hε i
      ⟨axisMap C ε hε referenceTriangle i z, _⟩)
    simpa only [minusLift_axisMap] using
      affineLift_holomorphic C referenceTriangle i (referenceTriangle.edgeEnd i)
  · change ContMDiff _ _ _ (fun z => minusLift C ε hε i
      ⟨axisMap C ε hε (upperNeighbour i) i z, _⟩)
    simpa only [minusLift_axisMap] using
      affineLift_holomorphic C (upperNeighbour i) i ((upperNeighbour i).edgeEnd i)

include hε1 hC hR

theorem plusLift_continuous (i : Fin 3) : Continuous (plusLift C ε hε i) := by
  let := curveChartedSpace C ε hε hε1 hC hR i
  exact (plusLift_holomorphic C ε hε hε1 hC hR i).continuous

theorem minusLift_continuous (i : Fin 3) : Continuous (minusLift C ε hε i) := by
  let := curveChartedSpace C ε hε hε1 hC hR i
  exact (minusLift_holomorphic C ε hε hε1 hC hR i).continuous

/-- The actual positive boundary projection, now as a homeomorphism. -/
def boundaryHomeomorph (i : Fin 3) :
    componentBoundary (edgeDirection i) ≃ₜ doubleCurve C ε hε i where
  toEquiv := boundaryEquiv C ε hε i
  continuous_toFun :=
    ((componentProjection_continuous C ε hε).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (plusLift_continuous C ε hε hε1 hC hR i).subtype_mk _

/-- The actual negative boundary projection, with the same double-curve target. -/
def negativeBoundaryHomeomorph (i : Fin 3) :
    componentBoundary (-edgeDirection i) ≃ₜ doubleCurve C ε hε i :=
  (oppositeBoundaryHomeomorph C ε hε hC (edgeDirection i)).symm.trans
    (boundaryHomeomorph C ε hε hε1 hC hR i)

theorem plusLift_isEmbedding (i : Fin 3) : IsEmbedding (plusLift C ε hε i) :=
  IsEmbedding.subtypeVal.comp (boundaryHomeomorph C ε hε hε1 hC hR i).symm.isEmbedding

theorem minusLift_isEmbedding (i : Fin 3) : IsEmbedding (minusLift C ε hε i) :=
  IsEmbedding.subtypeVal.comp
    (negativeBoundaryHomeomorph C ε hε hε1 hC hR i).symm.isEmbedding

end Wikipedia.HopfProblem.CuspQuotient.NormalizationCurves
