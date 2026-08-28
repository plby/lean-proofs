import Wikipedia.HopfProblem.DegreeCollapseNativeMorseHomologyZero

/-!
# A zero-handle creates a separate component

With empty attaching boundary the old space is clopen and excludes the
center of the new cell. Thus a connected total attachment forces the old
space to be empty. This is transferred through the actual native Morse
attachment, with no connectedness assumption on its lower sublevel.
-/

noncomputable section

open Set Metric Function Topology ContinuousMap

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open Wikipedia.SmoothSixDPoincare ManifoldMorse

theorem cell_old_empty_of_empty_boundary {N X : Type}
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace X] [PreconnectedSpace X]
    (D : EmbeddedCellAttachment N X) [IsEmpty (sphere (0 : N) 1)] : D.old = ∅ := by
  have hdisjoint (z : MorseHandle.UnitDisk N) : D.cell z ∉ D.old := by
    intro hz
    exact isEmptyElim (⟨z.val, mem_sphere_zero_iff_norm.mpr ((D.boundary z).mp hz)⟩ :
      sphere (0 : N) 1)
  have heq : D.old = (range D.cell)ᶜ := by
    ext x
    constructor
    · intro hx ⟨z, hz⟩
      exact hdisjoint z (hz ▸ hx)
    · intro hx
      have hc : x ∈ D.old ∪ range D.cell := by rw [D.cover]; trivial
      exact hc.resolve_right hx
  have hc : IsClopen D.old :=
    ⟨D.old_closed, heq.symm ▸ D.cell_closed.isClosed_range.isOpen_compl⟩
  rcases isClopen_iff.mp hc with h | h
  · exact h
  · let z : MorseHandle.UnitDisk N := ⟨0, by simp⟩
    exact False.elim (hdisjoint z (h ▸ mem_univ _))

theorem native_zero_handle_lower_isEmpty {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [T2Space M] {f : M → ℝ} {p : M} (d : MorseSurgeryData E f p)
    (hf : Continuous f) (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 0)
    [PathConnectedSpace {z : M // f z ≤ f p + d.radius ^ 2}] :
    IsEmpty {z : M // f z ≤ f p - d.radius ^ 2} := by
  let : Subsingleton d.chart.NegativeCoordinates :=
    (Module.finrank_eq_zero_iff_of_free ℝ d.chart.NegativeCoordinates).mp hindex
  let : IsEmpty (sphere (0 : d.chart.NegativeCoordinates) 1) := ⟨fun v => by
    have h := mem_sphere_zero_iff_norm.mp v.property
    rw [Subsingleton.elim v.val 0, norm_zero] at h
    norm_num at h⟩
  let : PathConnectedSpace
      ↥({z : M | f z ≤ f p - d.radius ^ 2} ∪ range d.coreMap) :=
    pathConnectedSpace_of_homotopyEquiv (d.coreUnionHomotopyEquiv hf)
  have he := cell_old_empty_of_empty_boundary (d.coreCellPresentation hf)
  refine ⟨fun x => ?_⟩
  have hx := (d.cellOldHomeomorph hf x).property
  exact (Set.eq_empty_iff_forall_notMem.mp he) _ hx

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
