import Wikipedia.SmoothSixDPoincare.MorseCellCover
import Wikipedia.SmoothSixDPoincare.CellAttachmentHomologySequence

/-!
# Native homology maps between original Morse sublevels

The boundary map is induced by the original attaching sphere. The old-space
map is induced by its actual whole-attachment realization. The upper-sublevel
connecting map is transported from the constructed core-cell sequence.
-/

noncomputable section

open Set Metric Function Topology ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

open Wikipedia.HopfProblem.SingularMayerVietoris
  Wikipedia.HopfProblem.PeriodTorusHigherHomology

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p)

open Classical in
def cellOldHomologyEquiv (hf : Continuous f) (k : ℕ) :
    SingularHomology {y : M // f y ≤ f p - d.radius ^ 2} k ≃ₗ[ℤ]
      SingularHomology (d.coreCellPresentation hf).old k :=
  homeomorphHomologyEquiv (d.cellOldHomeomorph hf) k

open Classical in
def cellTotalHomologyEquiv (hf : Continuous f) (k : ℕ) :
    SingularHomology ↥({y : M | f y ≤ f p - d.radius ^ 2} ∪ range d.coreMap) k ≃ₗ[ℤ]
      SingularHomology {y : M // f y ≤ f p + d.radius ^ 2} k :=
  homotopyEquivHomologyEquiv (d.coreUnionHomotopyEquiv hf) k

open Classical in
def coreBoundaryHomologyMap (k : ℕ) :
    SingularHomology (sphere (0 : d.chart.NegativeCoordinates) 1) k →ₗ[ℤ]
      SingularHomology {y : M // f y ≤ f p - d.radius ^ 2} k :=
  singularHomologyMap d.coreBoundaryMap k

open Classical in
def lowerRealizationHomologyMap (k : ℕ) :
    SingularHomology {y : M // f y ≤ f p - d.radius ^ 2} k →ₗ[ℤ]
      SingularHomology {y : M // f y ≤ f p + d.radius ^ 2} k :=
  singularHomologyMap d.realizedLowerInclusion k

open Classical in
def morseConnectingMap (hf : Continuous f) (k : ℕ) :
    SingularHomology {y : M // f y ≤ f p + d.radius ^ 2} (k + 1) →ₗ[ℤ]
      SingularHomology (sphere (0 : d.chart.NegativeCoordinates) 1) k :=
  ((d.coreCellPresentation hf).cellConnectingMap k).comp
    (d.cellTotalHomologyEquiv hf (k + 1)).symm.toLinearMap

open Classical in
theorem cellAttachingHomology_compare (hf : Continuous f) (k : ℕ)
    (a : SingularHomology (sphere (0 : d.chart.NegativeCoordinates) 1) k) :
    (d.coreCellPresentation hf).attachingHomologyMap k a =
      d.cellOldHomologyEquiv hf k (d.coreBoundaryHomologyMap k a) := by
  change singularHomologyMap (d.coreCellPresentation hf).attachingSphere k a =
    singularHomologyMap (d.cellOldHomeomorph hf).toHomotopyEquiv.toFun k
      (singularHomologyMap d.coreBoundaryMap k a)
  rw [d.coreCell_attaching_eq, singularHomologyMap_comp]
  rfl

open Classical in
theorem cellOldHomology_compare (hf : Continuous f) (k : ℕ)
    (a : SingularHomology {y : M // f y ≤ f p - d.radius ^ 2} k) :
    d.cellTotalHomologyEquiv hf k
      ((d.coreCellPresentation hf).oldHomologyMap k (d.cellOldHomologyEquiv hf k a)) =
        d.lowerRealizationHomologyMap k a := by
  change singularHomologyMap (d.coreUnionHomotopyEquiv hf).toFun k
    (singularHomologyMap (subtypeInclusion (d.coreCellPresentation hf).old) k
      (singularHomologyMap (d.cellOldHomeomorph hf).toHomotopyEquiv.toFun k a)) =
    singularHomologyMap d.realizedLowerInclusion k a
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp,
    ← LinearMap.comp_apply, ← singularHomologyMap_comp]
  rfl

open Classical in
theorem morseConnecting_compare (hf : Continuous f) (k : ℕ)
    (a : SingularHomology ↥({y : M | f y ≤ f p - d.radius ^ 2} ∪ range d.coreMap) (k + 1)) :
    d.morseConnectingMap hf k (d.cellTotalHomologyEquiv hf (k + 1) a) =
      (d.coreCellPresentation hf).cellConnectingMap k a := by
  change (d.coreCellPresentation hf).cellConnectingMap k
    ((d.cellTotalHomologyEquiv hf (k + 1)).symm (d.cellTotalHomologyEquiv hf (k + 1) a)) = _
  rw [LinearEquiv.symm_apply_apply]

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
