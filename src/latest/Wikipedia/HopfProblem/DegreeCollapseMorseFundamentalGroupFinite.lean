import Wikipedia.HopfProblem.DegreeCollapseCellFundamentalGroupFinite
import Wikipedia.SmoothSixDPoincare.MorseCellCover

/-!

# Finite generation across a positive-index native Morse handle

The original lower sublevel is identified with the old part of the actual
core-cell union. Positive-dimensional cells preserve finite generation,
including the disconnected zero-sphere overlap of a one-handle. The
constructed core homotopy equivalence returns to the original upper
sublevel. No finite-generation assertion about a replacement space is used.
-/

noncomputable section

open Set Metric Function Topology ContinuousMap

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseFiniteness

open Wikipedia.SmoothSixDPoincare ManifoldMorse

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p) (hf : Continuous f)
  [PathConnectedSpace {y : M // f y ≤ f p - d.radius ^ 2}]

include hf in
theorem upper_pathConnected_of_positive_index
    (hIndex : 0 < Module.finrank ℝ d.chart.NegativeCoordinates) :
    PathConnectedSpace {y : M // f y ≤ f p + d.radius ^ 2} := by
  let : PathConnectedSpace (d.coreCellPresentation hf).old :=
    FundamentalGroupTools.pathConnected_of_homotopyEquiv
      (d.cellOldHomeomorph hf).toHomotopyEquiv.symm
  let : PathConnectedSpace
      ↥({y : M | f y ≤ f p - d.radius ^ 2} ∪ range d.coreMap) :=
    AttachmentFiniteness.cell_pathConnected_of_positive_finrank
      (d.coreCellPresentation hf) hIndex
  exact FundamentalGroupTools.pathConnected_of_homotopyEquiv
    (d.coreUnionHomotopyEquiv hf).symm

include hf in
theorem upper_fundamentalGroup_finite_of_positive_index
    (hIndex : 0 < Module.finrank ℝ d.chart.NegativeCoordinates)
    (hOld : ∀ x : {y : M // f y ≤ f p - d.radius ^ 2},
      Group.FG (FundamentalGroup {y : M // f y ≤ f p - d.radius ^ 2} x))
    (x : {y : M // f y ≤ f p + d.radius ^ 2}) :
    Group.FG (FundamentalGroup {y : M // f y ≤ f p + d.radius ^ 2} x) := by
  let : PathConnectedSpace (d.coreCellPresentation hf).old :=
    FundamentalGroupTools.pathConnected_of_homotopyEquiv
      (d.cellOldHomeomorph hf).toHomotopyEquiv.symm
  have hOld' : ∀ y : (d.coreCellPresentation hf).old,
      Group.FG (FundamentalGroup (d.coreCellPresentation hf).old y) :=
    FundamentalGroupFiniteness.of_homotopyEquiv
      (d.cellOldHomeomorph hf).toHomotopyEquiv hOld
  exact FundamentalGroupFiniteness.of_homotopyEquiv (d.coreUnionHomotopyEquiv hf)
    (AttachmentFiniteness.cell_fg_of_positive_finrank
      (d.coreCellPresentation hf) hIndex hOld') x

end Wikipedia.HopfProblem.DegreeCollapse.MorseFiniteness
