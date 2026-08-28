import Wikipedia.SmoothSixDPoincare.CellAttachmentHomologySequence
import Wikipedia.HopfProblem.SphereHomologySuspensionOneZero

/-!
# An attached cell with connected boundary creates no first homology

The actual overlap-to-disk map is injective in degree zero, since both its
sphere model and its disk target are path connected. Exactness forces the
original degree-zero connecting map to vanish. The old-space inclusion is
therefore surjective on first homology, even if the old space is disconnected.
-/

noncomputable section

open Set Metric Function Topology ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.EmbeddedCellAttachment

open Wikipedia.HopfProblem.SingularMayerVietoris
  Wikipedia.HopfProblem.PeriodTorusHigherHomology Wikipedia.HopfProblem.SphereHomology

variable {N X : Type} [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace X]
  (D : EmbeddedCellAttachment N X) [PathConnectedSpace (sphere (0 : N) 1)]

theorem cellConnecting_zero_apply (a : SingularHomology X 1) :
    D.cellConnectingMap 0 a = 0 := by
  let : ContractibleSpace D.diskPatch := D.diskPatch_contractible
  let q : C(sphere (0 : N) 1, D.diskPatch) :=
    (ContinuousMap.inclusion inter_subset_right).comp D.overlapSphereEquiv.toFun
  have hc : D.overlapHomologyEquiv 0 (D.cellConnectingMap 0 a) ∈ LinearMap.ker
      (leftHomologyMap D.oldNeighborhood D.diskPatch 0) := by
    rw [← exact_at_intersection D.oldNeighborhood D.diskPatch
      D.isOpen_oldNeighborhood D.isOpen_diskPatch D.open_cover 0]
    exact (D.mem_range_cellConnecting 0 _).mp ⟨a, rfl⟩
  change leftHomologyMap D.oldNeighborhood D.diskPatch 0
    (D.overlapHomologyEquiv 0 (D.cellConnectingMap 0 a)) = 0 at hc
  have h := congrArg Prod.snd hc
  rw [leftHomologyMap_apply] at h
  have hz : singularHomologyMap q 0 (D.cellConnectingMap 0 a) = 0 := by
    rw [singularHomologyMap_comp]
    exact neg_eq_zero.mp h
  apply singularHomologyMap_zero_injective q
  exact hz.trans (map_zero _).symm

theorem oldHomologyMap_one_surjective : Surjective (D.oldHomologyMap 1) := by
  intro a
  have ha : a ∈ LinearMap.ker (D.cellConnectingMap 0) := D.cellConnecting_zero_apply a
  rw [← D.cell_exact_at_ambient 0] at ha
  exact ha

theorem homologyOne_subsingleton_of_old [Subsingleton (SingularHomology D.old 1)] :
    Subsingleton (SingularHomology X 1) := D.oldHomologyMap_one_surjective.subsingleton

end Wikipedia.SmoothSixDPoincare.EmbeddedCellAttachment
