import Wikipedia.SmoothSixDPoincare.HandleCoreCellPresentation
import Wikipedia.SmoothSixDPoincare.CellFundamentalGroupCover

/-!
# Fundamental-group propagation through a whole embedded handle

The old space, the core-cell subspace, and the whole attachment are linked
by the original inclusions. The core deformation identifies the induced
map on fundamental groups without replacing the actual old-space map.
-/

noncomputable section

open Set Metric Function Topology ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.HandleCoreAttachment

open MorseHandle

variable {N P R X : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
  [FiniteDimensional ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P]
  [TopologicalSpace R] [TopologicalSpace X] [T2Space X]
  (r : R → X) (h : C(UnitDisk N × UnitDisk P, X))
  (hr : IsClosedEmbedding r) (hh : IsClosedEmbedding h)
  (hcover : range r ∪ range h = univ)
  (hface : ∀ z, h z ∈ range r ↔ ‖(z.1 : N)‖ = 1)
  [PathConnectedSpace R] [PathConnectedSpace (sphere (0 : N) 1)]

include hr hh hcover hface in
omit [PathConnectedSpace (sphere (0 : N) 1)] in
theorem total_pathConnected [Nonempty (sphere (0 : N) 1)] : PathConnectedSpace X := by
  let D := cellPresentation r h hr hh hface
  let e := cellOldHomeomorph r h hr hh hface
  let _ : PathConnectedSpace D.old :=
    FundamentalGroupTools.pathConnected_of_homotopyEquiv e.symm.toHomotopyEquiv
  let _ : PathConnectedSpace (coreSpace r h) := D.total_pathConnected_of_sphere_nonempty
  exact FundamentalGroupTools.pathConnected_of_homotopyEquiv
    (homotopyEquiv r h hr hh hcover hface).symm

include hh hcover hface in
theorem old_fundamentalGroup_surjective (x : R) :
    Surjective (FundamentalGroup.map ⟨r, hr.continuous⟩ x) := by
  let D := cellPresentation r h hr hh hface
  let e := cellOldHomeomorph r h hr hh hface
  let q := homotopyEquiv r h hr hh hcover hface
  let _ : PathConnectedSpace D.old :=
    FundamentalGroupTools.pathConnected_of_homotopyEquiv e.symm.toHomotopyEquiv
  rw [← cell_old_realization r h hr hh hcover hface, FundamentalGroupTools.map_comp,
    FundamentalGroupTools.map_comp]
  exact (FundamentalGroupTools.map_bijective_of_homotopyEquiv q _).2.comp
    ((D.old_inclusion_fundamentalGroup_surjective (e x)).comp
      (FundamentalGroupTools.map_bijective_of_homotopyEquiv e.toHomotopyEquiv x).2)

include hh hcover hface in
theorem old_fundamentalGroup_bijective [SimplyConnectedSpace (sphere (0 : N) 1)]
    (x : R) : Bijective (FundamentalGroup.map ⟨r, hr.continuous⟩ x) := by
  let D := cellPresentation r h hr hh hface
  let e := cellOldHomeomorph r h hr hh hface
  let q := homotopyEquiv r h hr hh hcover hface
  let _ : PathConnectedSpace D.old :=
    FundamentalGroupTools.pathConnected_of_homotopyEquiv e.symm.toHomotopyEquiv
  rw [← cell_old_realization r h hr hh hcover hface, FundamentalGroupTools.map_comp,
    FundamentalGroupTools.map_comp]
  exact (FundamentalGroupTools.map_bijective_of_homotopyEquiv q _).comp
    ((D.old_inclusion_fundamentalGroup_bijective (e x)).comp
      (FundamentalGroupTools.map_bijective_of_homotopyEquiv e.toHomotopyEquiv x))

end Wikipedia.SmoothSixDPoincare.HandleCoreAttachment
