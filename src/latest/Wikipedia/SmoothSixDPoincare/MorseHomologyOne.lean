import Wikipedia.SmoothSixDPoincare.CellAttachmentHomologyOne
import Wikipedia.SmoothSixDPoincare.MorseCellHomologySequence
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Handles of index at least two create no first homology

The actual boundary sphere is path connected by its dimension. The native
cell-cover calculation forces the degree-zero Morse connecting map to
vanish. Hence the realized lower-sublevel map is surjective in degree one.
-/

noncomputable section

open Set Metric Function Topology ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

open Wikipedia.HopfProblem.SingularMayerVietoris

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p)

omit [T2Space M] in
theorem attachingSphere_pathConnected
    (hindex : 2 ≤ Module.finrank ℝ d.chart.NegativeCoordinates) :
    PathConnectedSpace (sphere (0 : d.chart.NegativeCoordinates) 1) :=
  isPathConnected_iff_pathConnectedSpace.mp
    (isPathConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by omega)) _ zero_le_one)

theorem morseConnecting_zero_apply (hf : Continuous f)
    (hindex : 2 ≤ Module.finrank ℝ d.chart.NegativeCoordinates)
    (a : SingularHomology {y : M // f y ≤ f p + d.radius ^ 2} 1) :
    d.morseConnectingMap hf 0 a = 0 := by
  let := d.attachingSphere_pathConnected hindex
  exact (d.coreCellPresentation hf).cellConnecting_zero_apply _

theorem lowerRealization_one_surjective (hf : Continuous f)
    (hindex : 2 ≤ Module.finrank ℝ d.chart.NegativeCoordinates) :
    Surjective (d.lowerRealizationHomologyMap 1) := by
  intro a
  have ha : a ∈ LinearMap.ker (d.morseConnectingMap hf 0) :=
    d.morseConnecting_zero_apply hf hindex a
  rw [← d.morse_exact_at_upper hf 0] at ha
  exact ha

theorem upperHomologyOne_subsingleton (hf : Continuous f)
    (hindex : 2 ≤ Module.finrank ℝ d.chart.NegativeCoordinates)
    [Subsingleton (SingularHomology {y : M // f y ≤ f p - d.radius ^ 2} 1)] :
    Subsingleton (SingularHomology {y : M // f y ≤ f p + d.radius ^ 2} 1) :=
  (d.lowerRealization_one_surjective hf hindex).subsingleton

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
