import Wikipedia.SmoothSixDPoincare.CellCoverHomotopy
import Wikipedia.SmoothSixDPoincare.OpenCoverFundamentalGroupKernel
import Wikipedia.SmoothSixDPoincare.FundamentalGroupMapTools
import Wikipedia.HopfProblem.FundamentalGroupBasepointNaturality
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Fundamental groups of the actual embedded-cell open cover

The old-space neighborhood and the open disk are the original subsets of
the attached space. Their overlap is the original annulus, with a chosen
point on its sphere. Van Kampen therefore describes the actual inclusion,
not an abstract group assigned to the attachment.
-/

noncomputable section

open Set Metric Function ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.EmbeddedCellAttachment

open Wikipedia.HopfProblem.FundamentalGroupVanKampen

variable {N X : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace X]
  (D : EmbeddedCellAttachment N X) [PathConnectedSpace D.old]
  [PathConnectedSpace (sphere (0 : N) 1)]

omit [PathConnectedSpace (sphere (0 : N) 1)] in
theorem oldNeighborhood_pathConnected : PathConnectedSpace D.oldNeighborhood :=
  FundamentalGroupTools.pathConnected_of_homotopyEquiv D.oldHomotopyEquiv.symm

omit [PathConnectedSpace D.old] in
theorem overlap_pathConnected : PathConnectedSpace ↥(D.oldNeighborhood ∩ D.diskPatch) :=
  FundamentalGroupTools.pathConnected_of_homotopyEquiv D.overlapSphereEquiv.symm

omit [PathConnectedSpace (sphere (0 : N) 1)] in
include D in
theorem total_pathConnected_of_sphere_nonempty [Nonempty (sphere (0 : N) 1)] :
    PathConnectedSpace X := by
  let _ : ContractibleSpace (MorseHandle.UnitDisk N) :=
    (convex_closedBall (0 : N) 1).contractibleSpace ⟨0, by simp⟩
  let u := Classical.arbitrary (sphere (0 : N) 1)
  let z : MorseHandle.UnitDisk N := ⟨u.val, sphere_subset_closedBall u.property⟩
  have hz : D.cell z ∈ D.old := (D.boundary z).mpr (mem_sphere_zero_iff_norm.mp u.property)
  have ho : IsPathConnected D.old := isPathConnected_iff_pathConnectedSpace.mpr inferInstance
  have h := ho.union (isPathConnected_range D.cell.continuous) ⟨D.cell z, hz, mem_range_self z⟩
  rw [D.cover] at h
  exact pathConnectedSpace_iff_univ.mpr h

def fundamentalGroupCover (u : sphere (0 : N) 1) : TwoOpenCover X where
  U := ⟨D.oldNeighborhood, D.isOpen_oldNeighborhood⟩
  V := ⟨D.diskPatch, D.isOpen_diskPatch⟩
  cover := D.open_cover
  pathConnectedU := isPathConnected_iff_pathConnectedSpace.mpr D.oldNeighborhood_pathConnected
  pathConnectedV := by
    let _ := D.diskPatch_contractible
    exact isPathConnected_iff_pathConnectedSpace.mpr inferInstance
  pathConnectedIntersection := isPathConnected_iff_pathConnectedSpace.mpr D.overlap_pathConnected
  base := (D.overlapSphereEquiv u).val
  baseU := (D.overlapSphereEquiv u).property.1
  baseV := (D.overlapSphereEquiv u).property.2

include D in
theorem total_pathConnected : PathConnectedSpace X := by
  let C := D.fundamentalGroupCover (Classical.arbitrary (sphere (0 : N) 1))
  have h := C.pathConnectedU.union C.pathConnectedV ⟨C.base, C.baseU, C.baseV⟩
  rw [C.cover] at h
  exact pathConnectedSpace_iff_univ.mpr h

theorem fundamentalGroupCover_VGroup_subsingleton (u : sphere (0 : N) 1) :
    Subsingleton (D.fundamentalGroupCover u).VGroup := by
  let _ := D.diskPatch_contractible
  exact inferInstanceAs (Subsingleton (FundamentalGroup D.diskPatch
    ⟨(D.overlapSphereEquiv u).val, (D.overlapSphereEquiv u).property.2⟩))

theorem fundamentalGroupCover_inclusion_surjective (u : sphere (0 : N) 1) :
    Surjective (D.fundamentalGroupCover u).inclusionHomU := by
  let _ := D.fundamentalGroupCover_VGroup_subsingleton u
  exact OpenCoverFundamentalGroup.inclusion_surjective (D.fundamentalGroupCover u)

theorem fundamentalGroupCover_inclusion_kernel (u : sphere (0 : N) 1) :
    (D.fundamentalGroupCover u).inclusionHomU.ker =
      Subgroup.normalClosure (range (D.fundamentalGroupCover u).overlapHomU) := by
  let _ := D.fundamentalGroupCover_VGroup_subsingleton u
  exact OpenCoverFundamentalGroup.inclusion_kernel (D.fundamentalGroupCover u)

theorem fundamentalGroupCover_inclusion_bijective [SimplyConnectedSpace (sphere (0 : N) 1)]
    (u : sphere (0 : N) 1) : Bijective (D.fundamentalGroupCover u).inclusionHomU := by
  let _ := D.fundamentalGroupCover_VGroup_subsingleton u
  let _ : SimplyConnectedSpace ↥(D.oldNeighborhood ∩ D.diskPatch) :=
    D.overlapSphereEquiv.symm.simplyConnectedSpace
  let _ : Subsingleton (D.fundamentalGroupCover u).OverlapGroup := by
    exact inferInstanceAs (Subsingleton
      (FundamentalGroup ↥(D.oldNeighborhood ∩ D.diskPatch) (D.overlapSphereEquiv u)))
  exact OpenCoverFundamentalGroup.inclusion_bijective_of_trivial_overlap
    (D.fundamentalGroupCover u)

/-- Attaching a cell with connected boundary adds no fundamental-group generators. -/
theorem old_inclusion_fundamentalGroup_surjective (x : D.old) :
    Surjective (FundamentalGroup.map ⟨Subtype.val, continuous_subtype_val⟩ x) := by
  let u := Classical.arbitrary (sphere (0 : N) 1)
  let _ := D.oldNeighborhood_pathConnected
  let f : C(D.oldNeighborhood, X) := ⟨Subtype.val, continuous_subtype_val⟩
  have hf : Surjective (FundamentalGroup.map f (D.oldInclusion x)) :=
    Wikipedia.HopfProblem.fundamentalGroup_map_surjective_at_of_pathConnected f
      (D.fundamentalGroupCover u).baseUPoint (D.oldInclusion x)
      (D.fundamentalGroupCover_inclusion_surjective u)
  have hi := FundamentalGroupTools.map_bijective_of_homotopyEquiv D.oldHomotopyEquiv x
  have heq : f.comp D.oldInclusion = ⟨Subtype.val, continuous_subtype_val⟩ := rfl
  rw [← heq, FundamentalGroupTools.map_comp]
  exact hf.comp hi.2

/-- With simply connected boundary, the actual old-space inclusion is an isomorphism on π₁. -/
theorem old_inclusion_fundamentalGroup_bijective [SimplyConnectedSpace (sphere (0 : N) 1)]
    (x : D.old) :
    Bijective (FundamentalGroup.map ⟨Subtype.val, continuous_subtype_val⟩ x) := by
  let u := Classical.arbitrary (sphere (0 : N) 1)
  let _ := D.oldNeighborhood_pathConnected
  let f : C(D.oldNeighborhood, X) := ⟨Subtype.val, continuous_subtype_val⟩
  have hf : Bijective (FundamentalGroup.map f (D.oldInclusion x)) :=
    Wikipedia.HopfProblem.fundamentalGroup_map_bijective_at_of_pathConnected f
      (D.fundamentalGroupCover u).baseUPoint (D.oldInclusion x)
      (D.fundamentalGroupCover_inclusion_bijective u)
  have hi := FundamentalGroupTools.map_bijective_of_homotopyEquiv D.oldHomotopyEquiv x
  have heq : f.comp D.oldInclusion = ⟨Subtype.val, continuous_subtype_val⟩ := rfl
  rw [← heq, FundamentalGroupTools.map_comp]
  exact hf.comp hi

end Wikipedia.SmoothSixDPoincare.EmbeddedCellAttachment
