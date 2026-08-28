import Wikipedia.SmoothSixDPoincare.CellOldNeighborhoodDeformation
import Wikipedia.SmoothSixDPoincare.DiskAnnulusHomotopy

/-!
# The actual cell-cover homotopy identifications and attaching map

The disk patch is contractible. The annular overlap has the homotopy type
of the original boundary sphere. Composing its original inclusion with the
constructed old-neighborhood retraction gives exactly the attaching map.
-/

noncomputable section

open Set Metric Topology ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.EmbeddedCellAttachment

variable {N X : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace X]
  (D : EmbeddedCellAttachment N X)

theorem diskPatch_contractible : ContractibleSpace D.diskPatch := by
  let : ContractibleSpace (DiskAnnulus.OpenDisk N) := DiskAnnulus.openDisk_contractible
  exact D.diskHomeomorph.symm.contractibleSpace

def overlapSphereEquiv : sphere (0 : N) 1 ≃ₕ ↥(D.oldNeighborhood ∩ D.diskPatch) :=
  DiskAnnulus.sphereHomotopyEquiv.trans D.overlapHomeomorph.toHomotopyEquiv

def overlapOldMap : C(↥(D.oldNeighborhood ∩ D.diskPatch), D.old) :=
  D.oldRetraction.comp (ContinuousMap.inclusion inter_subset_left)

/-- The overlap sphere maps to the old space by the original attaching sphere, point for point. -/
theorem overlapOldMap_sphere (u : sphere (0 : N) 1) :
    D.overlapOldMap (D.overlapSphereEquiv u) = D.attachingSphere u := by
  let z : OuterDisk.Space N :=
    ⟨(DiskAnnulus.fromSphere u).val, (DiskAnnulus.fromSphere u).property.1⟩
  change D.oldRetraction (D.outerInclusion z) = D.attachingSphere u
  rw [D.oldRetraction_outer]
  apply congrArg D.attachingSphere
  exact DiskAnnulus.toSphere_fromSphere u

theorem overlapOldMap_comp_sphere :
    D.overlapOldMap.comp D.overlapSphereEquiv.toFun = D.attachingSphere :=
  ContinuousMap.ext D.overlapOldMap_sphere

end Wikipedia.SmoothSixDPoincare.EmbeddedCellAttachment
