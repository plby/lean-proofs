import Wikipedia.HopfProblem.CuspNormalizationSheafLocalCoordinatesAxisChartsBasic

/-!
# Holomorphic charts on the double curves from arbitrary triangles

Every toric coordinate axis is an affine parametrization of its actual
quotient double curve.  Composing the defining sphere charts with the
proved scalar change gives an open partial homeomorphism whose inverse
belongs to the existing maximal analytic atlas.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspQuotient.NormalizationLocalCoordinates

open ToricCharts ToricSpace ToricFan Triangle

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

include hε1 hC hR in
theorem axisSection_isOpenEmbedding (s : Triangle) (i : Fin 3) :
    IsOpenEmbedding (axisSection C ε hε s i) := by
  let := quotient_t2Space C ε hε hε1 hC hR
  rw [axisSection_eq_affineMap_scaled]
  exact ((curveCharts C ε hε i).affineMap_isOpenEmbedding s.upper).comp
    (axisScaleHomeomorph C s i).isOpenEmbedding

/-- The genuine affine parametrization associated to an arbitrary triangle. -/
def axisParametrization (s : Triangle) (i : Fin 3) :
    OpenPartialHomeomorph ℂ (doubleCurve C ε hε i) := by
  let := quotient_t2Space C ε hε hε1 hC hR
  exact (axisScaleHomeomorph C s i).toOpenPartialHomeomorph.trans
    ((curveCharts C ε hε i).parametrization s.upper)

@[simp] theorem axisParametrization_apply (s : Triangle) (i : Fin 3) (z : ℂ) :
    axisParametrization C ε hε hε1 hC hR s i z = axisSection C ε hε s i z := by
  let := quotient_t2Space C ε hε hε1 hC hR
  change (curveCharts C ε hε i).affineMap s.upper (axisScale C s i z) = _
  exact (congrFun (axisSection_eq_affineMap_scaled C ε hε s i) z).symm

@[simp] theorem axisParametrization_coe (s : Triangle) (i : Fin 3) (z : ℂ) :
    (axisParametrization C ε hε hε1 hC hR s i z : QuotientSpace C ε) =
      axisMap C ε hε s i z := by
  rw [axisParametrization_apply, axisSection_coe]

@[simp] theorem axisParametrization_source (s : Triangle) (i : Fin 3) :
    (axisParametrization C ε hε hε1 hC hR s i).source = univ := by
  let := quotient_t2Space C ε hε hε1 hC hR
  simp [axisParametrization]

@[simp] theorem axisParametrization_target (s : Triangle) (i : Fin 3) :
    (axisParametrization C ε hε hε1 hC hR s i).target =
      range (axisSection C ε hε s i) := by
  let := quotient_t2Space C ε hε hε1 hC hR
  simp [axisParametrization, axisSection_range]

@[simp] theorem axisParametrization_symm_apply (s : Triangle) (i : Fin 3) (z : ℂ) :
    (axisParametrization C ε hε hε1 hC hR s i).symm
      (axisSection C ε hε s i z) = z := by
  have h := (axisParametrization C ε hε hε1 hC hR s i).left_inv
    (show z ∈ (axisParametrization C ε hε hε1 hC hR s i).source by simp)
  simpa only [axisParametrization_apply] using h

theorem axisSection_mem_target (s : Triangle) (i : Fin 3) (z : ℂ) :
    axisSection C ε hε s i z ∈ (axisParametrization C ε hε hε1 hC hR s i).target := by
  rw [axisParametrization_target]
  exact mem_range_self z

theorem axisSection_holomorphic (s : Triangle) (i : Fin 3) :
    letI := curveChartedSpace C ε hε hε1 hC hR i
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω
      (axisSection C ε hε s i) := by
  let := quotient_t2Space C ε hε hε1 hC hR
  let := curveChartedSpace C ε hε hε1 hC hR i
  rw [axisSection_eq_affineMap_scaled]
  exact ((curveCharts C ε hε i).affineMap_holomorphic s.upper).comp
    (axisScale_holomorphic C s i).contMDiff

theorem axisParametrization_holomorphic (s : Triangle) (i : Fin 3) :
    letI := curveChartedSpace C ε hε hε1 hC hR i
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω
      (axisParametrization C ε hε hε1 hC hR s i) := by
  let := curveChartedSpace C ε hε hε1 hC hR i
  have h := axisSection_holomorphic C ε hε hε1 hC hR s i
  exact h.congr (fun z => axisParametrization_apply C ε hε hε1 hC hR s i z)

theorem axisParametrization_symm_holomorphic (s : Triangle) (i : Fin 3) :
    letI := curveChartedSpace C ε hε hε1 hC hR i
    ContMDiffOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω
      (axisParametrization C ε hε hε1 hC hR s i).symm
      (range (axisSection C ε hε s i)) := by
  let := quotient_t2Space C ε hε hε1 hC hR
  let := curveChartedSpace C ε hε hε1 hC hR i
  let := curve_isManifold C ε hε hε1 hC hR i
  change ContMDiffOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω
    (axisScaleInv C s i ∘ ((curveCharts C ε hε i).parametrization s.upper).symm)
    (range (axisSection C ε hε s i))
  have hc : ((curveCharts C ε hε i).parametrization s.upper).symm ∈
      IsManifold.maximalAtlas (modelWithCornersSelf ℂ ℂ) ω (doubleCurve C ε hε i) :=
    IsManifold.subset_maximalAtlas (mem_range_self s.upper)
  have hh := (axisScaleInv_holomorphic C s i).contMDiff.comp_contMDiffOn
    (contMDiffOn_of_mem_maximalAtlas hc)
  simpa only [OpenPartialHomeomorph.symm_source, TwoAffineCharts.parametrization_target,
    axisSection_range] using hh

/-- This inverse chart is in the existing double-curve maximal analytic atlas. -/
theorem axisParametrization_mem_maximalAtlas (s : Triangle) (i : Fin 3) :
    letI := curveChartedSpace C ε hε hε1 hC hR i
    (axisParametrization C ε hε hε1 hC hR s i).symm ∈
      IsManifold.maximalAtlas (modelWithCornersSelf ℂ ℂ) ω (doubleCurve C ε hε i) := by
  let := curveChartedSpace C ε hε hε1 hC hR i
  let := curve_isManifold C ε hε hε1 hC hR i
  apply (axisParametrization C ε hε hε1 hC hR s i).symm.mem_maximalAtlas_of_contMDiffOn
  · simpa only [OpenPartialHomeomorph.symm_source, axisParametrization_target] using
      axisParametrization_symm_holomorphic C ε hε hε1 hC hR s i
  · exact (axisParametrization_holomorphic C ε hε hε1 hC hR s i).contMDiffOn

end Wikipedia.HopfProblem.CuspQuotient.NormalizationLocalCoordinates
