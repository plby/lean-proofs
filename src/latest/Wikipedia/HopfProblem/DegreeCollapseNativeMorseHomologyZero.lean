import Wikipedia.HopfProblem.DegreeCollapseAttachmentHomologyZero
import Wikipedia.HopfProblem.DegreeCollapsePointClassComponents
import Wikipedia.SmoothSixDPoincare.MorseHomologyOne

/-!
# Native handles of index at least two preserve components

The map is the original whole-attachment realization. Its degree-zero
homology map is bijective and reflects actual paths between lower-sublevel
points. In particular, a connected upper sublevel forces a connected lower
sublevel; no connectedness premise on the latter is assumed.
-/

noncomputable section

open Set Metric Function Topology ContinuousMap

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open Wikipedia.SmoothSixDPoincare.ManifoldMorse SingularMayerVietoris

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p)

theorem native_lowerRealization_zero_bijective (hf : Continuous f)
    (hindex : 2 ≤ Module.finrank ℝ d.chart.NegativeCoordinates) :
    Bijective (d.lowerRealizationHomologyMap 0) := by
  let := d.attachingSphere_pathConnected hindex
  have hi := cell_oldHomologyMap_zero_bijective (d.coreCellPresentation hf)
  have heq : d.lowerRealizationHomologyMap 0 =
      (d.cellTotalHomologyEquiv hf 0).toLinearMap.comp
        (((d.coreCellPresentation hf).oldHomologyMap 0).comp
          (d.cellOldHomologyEquiv hf 0).toLinearMap) := by
    ext a
    exact (d.cellOldHomology_compare hf 0 a).symm
  rw [heq]
  exact (d.cellTotalHomologyEquiv hf 0).bijective.comp
    (hi.comp (d.cellOldHomologyEquiv hf 0).bijective)

theorem native_lowerRealization_joined_iff (hf : Continuous f)
    (hindex : 2 ≤ Module.finrank ℝ d.chart.NegativeCoordinates)
    (x y : {z : M // f z ≤ f p - d.radius ^ 2}) :
    Joined (d.realizedLowerInclusion x) (d.realizedLowerInclusion y) ↔ Joined x y :=
  joined_iff_of_homologyZero_injective d.realizedLowerInclusion
    (native_lowerRealization_zero_bijective d hf hindex).1 x y

theorem native_lower_pathConnected_of_upper (hf : Continuous f)
    (hindex : 2 ≤ Module.finrank ℝ d.chart.NegativeCoordinates)
    [PathConnectedSpace {z : M // f z ≤ f p + d.radius ^ 2}] :
    PathConnectedSpace {z : M // f z ≤ f p - d.radius ^ 2} := by
  let := d.attachingSphere_pathConnected hindex
  let : Nonempty {z : M // f z ≤ f p - d.radius ^ 2} :=
    ⟨d.coreBoundaryMap (Classical.arbitrary (sphere (0 : d.chart.NegativeCoordinates) 1))⟩
  exact pathConnectedSpace_of_homologyZero_injective d.realizedLowerInclusion
    (native_lowerRealization_zero_bijective d hf hindex).1

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
