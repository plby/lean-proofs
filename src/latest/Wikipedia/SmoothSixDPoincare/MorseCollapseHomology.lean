import Wikipedia.SmoothSixDPoincare.CellCollapseHomology
import Wikipedia.SmoothSixDPoincare.MorseOnePointCollapse
import Wikipedia.SmoothSixDPoincare.MorseCellHomologySequence

/-!
# The original Morse collapse realizes the native homology connecting map

Transport the actual cell-collapse comparison through the same retained
whole-attachment realization. The resulting kernel is exactly the image
of the original lower-sublevel homology map, not an assigned cell matrix.
-/

noncomputable section

open Set Metric Topology ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

open Wikipedia.HopfProblem.SingularMayerVietoris
  Wikipedia.HopfProblem.PeriodTorusHigherHomology

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p)

open Classical in
theorem upperCollapseHomology_coreCell (hf : Continuous f) (k : ℕ)
    (a : SingularHomology ↥({y : M | f y ≤ f p - d.radius ^ 2} ∪ range d.coreMap) k) :
    singularHomologyMap (d.upperCollapseMap hf) k (d.cellTotalHomologyEquiv hf k a) =
      singularHomologyMap (d.coreCellPresentation hf).collapseMap k a := by
  change singularHomologyMap (d.upperCollapseMap hf) k
    (singularHomologyMap (d.coreUnionHomotopyEquiv hf).toFun k a) = _
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp, d.upperCollapse_coreCell]

open Classical in
/-- The original upper-sublevel collapse induces exactly the native connecting map. -/
theorem upperCollapse_connecting_compare (hf : Continuous f) (k : ℕ)
    (a : SingularHomology {y : M // f y ≤ f p + d.radius ^ 2} (k + 1)) :
    OnePointCover.sphereConnecting OnePointCover.overlapRadius
      OnePointCover.overlapRadius_pos k
        (singularHomologyMap (d.upperCollapseMap hf) (k + 1) a) =
      d.morseConnectingMap hf k a := by
  obtain ⟨b, rfl⟩ := (d.cellTotalHomologyEquiv hf (k + 1)).surjective a
  rw [d.upperCollapseHomology_coreCell,
    (d.coreCellPresentation hf).collapse_connecting_compare, d.morseConnecting_compare]

open Classical in
theorem upperCollapse_homology_equiv_compare (hf : Continuous f) (k : ℕ)
    (a : SingularHomology {y : M // f y ≤ f p + d.radius ^ 2} (k + 2)) :
    OnePointCover.sphereHomologyEquiv OnePointCover.overlapRadius
      OnePointCover.overlapRadius_pos k
        (singularHomologyMap (d.upperCollapseMap hf) (k + 2) a) =
      d.morseConnectingMap hf (k + 1) a :=
  d.upperCollapse_connecting_compare hf (k + 1) a

open Classical in
/-- The actual collapse kills exactly the classes supplied by the realized lower sublevel. -/
theorem upperCollapse_homology_kernel (hf : Continuous f) (k : ℕ) :
    LinearMap.ker (singularHomologyMap (d.upperCollapseMap hf) (k + 1)) =
      LinearMap.range (d.lowerRealizationHomologyMap (k + 1)) := by
  rw [d.morse_exact_at_upper hf k]
  ext a
  change singularHomologyMap (d.upperCollapseMap hf) (k + 1) a = 0 ↔
    d.morseConnectingMap hf k a = 0
  rw [← d.upperCollapse_connecting_compare]
  constructor
  · intro h
    rw [h, map_zero]
  · intro h
    exact (OnePointCover.sphereConnecting_injective OnePointCover.overlapRadius
      OnePointCover.overlapRadius_pos k) (h.trans (map_zero _).symm)

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
