import Wikipedia.HopfProblem.DegreeCollapseCellComponentCriterion
import Wikipedia.HopfProblem.DegreeCollapseNativeMorseHomologyZero

/-!
# The old components met by an actual native handle

If the whole attaching sphere lands in one path component of the original
lower sublevel, connectedness of the upper sublevel descends. At positive
index, failure of this condition gives two actual attaching-sphere points
whose images lie in distinct lower-sublevel components.
-/

noncomputable section

open Set Metric Function Topology ContinuousMap

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open Wikipedia.SmoothSixDPoincare ManifoldMorse

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p)

theorem native_lower_pathConnected_of_attaching_component (hf : Continuous f)
    (a : {z : M // f z ≤ f p - d.radius ^ 2})
    (hcomponent : ∀ u, Joined (d.coreBoundaryMap u) a)
    [PathConnectedSpace {z : M // f z ≤ f p + d.radius ^ 2}] :
    PathConnectedSpace {z : M // f z ≤ f p - d.radius ^ 2} := by
  let : PathConnectedSpace
      ↥({z : M | f z ≤ f p - d.radius ^ 2} ∪ range d.coreMap) :=
    pathConnectedSpace_of_homotopyEquiv (d.coreUnionHomotopyEquiv hf)
  let : PathConnectedSpace (d.coreCellPresentation hf).old :=
    cell_old_pathConnected_of_attaching_component (d.coreCellPresentation hf)
      (d.cellOldHomeomorph hf a) (fun u => by
        rw [d.coreCell_attaching_eq]
        exact (hcomponent u).map (d.cellOldHomeomorph hf).continuous)
  exact pathConnectedSpace_of_homotopyEquiv (d.cellOldHomeomorph hf).toHomotopyEquiv

theorem native_attaching_component_of_pairwise_joined
    (hindex : 0 < Module.finrank ℝ d.chart.NegativeCoordinates)
    (hjoined : ∀ u v, Joined (d.coreBoundaryMap u) (d.coreBoundaryMap v)) :
    ∃ a : {z : M // f z ≤ f p - d.radius ^ 2}, ∀ u, Joined (d.coreBoundaryMap u) a := by
  let : Nontrivial d.chart.NegativeCoordinates := Module.nontrivial_of_finrank_pos hindex
  obtain ⟨v, hv⟩ : (sphere (0 : d.chart.NegativeCoordinates) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  exact ⟨d.coreBoundaryMap ⟨v, hv⟩, fun u => hjoined u ⟨v, hv⟩⟩

theorem native_attaching_distinct_components_of_not_one_component
    (hindex : 0 < Module.finrank ℝ d.chart.NegativeCoordinates)
    (hnot : ¬∃ a : {z : M // f z ≤ f p - d.radius ^ 2},
      ∀ u, Joined (d.coreBoundaryMap u) a) :
    ∃ u v, ¬Joined (d.coreBoundaryMap u) (d.coreBoundaryMap v) := by
  classical
  by_contra h
  push_neg at h
  exact hnot (native_attaching_component_of_pairwise_joined d hindex h)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
