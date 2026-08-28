import Wikipedia.HopfProblem.DegreeCollapseAttachmentHomologyZero
import Wikipedia.HopfProblem.DegreeCollapseZeroHomologyGenerators

/-!
# Exactly when an attachment can merge old components

The kernel of the actual old-space map consists of attaching classes whose
disk class vanishes. In particular, an attaching sphere whose image lies in
one old path component cannot merge two old components, even when the sphere
itself is disconnected. This includes loop-type one-handles.
-/

noncomputable section

open Set Metric Function Topology ContinuousMap

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open Wikipedia.SmoothSixDPoincare SingularMayerVietoris PeriodTorusHigherHomology

variable {N X : Type} [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace X]
  (D : EmbeddedCellAttachment N X)

def cellDiskBoundaryHomologyMap : SingularHomology (sphere (0 : N) 1) 0 →ₗ[ℤ]
    SingularHomology D.diskPatch 0 :=
  singularHomologyMap
    ((ContinuousMap.inclusion inter_subset_right).comp D.overlapSphereEquiv.toFun) 0

theorem cell_oldHomologyMap_zero_iff (a : SingularHomology D.old 0) :
    D.oldHomologyMap 0 a = 0 ↔ ∃ z : SingularHomology (sphere (0 : N) 1) 0,
      D.attachingHomologyMap 0 z = a ∧ cellDiskBoundaryHomologyMap D z = 0 := by
  constructor
  · intro ha
    have hp : (D.oldHomologyEquiv 0 a, 0) ∈
        LinearMap.ker (rightHomologyMap D.oldNeighborhood D.diskPatch 0) := by
      change rightHomologyMap D.oldNeighborhood D.diskPatch 0 (D.oldHomologyEquiv 0 a, 0) = 0
      rw [D.coverRight_old]
      exact ha
    rw [← exact_at_pair D.oldNeighborhood D.diskPatch
      D.isOpen_oldNeighborhood D.isOpen_diskPatch D.open_cover 0] at hp
    obtain ⟨c, hc⟩ := hp
    let z := (D.overlapHomologyEquiv 0).symm c
    have hL : leftHomologyMap D.oldNeighborhood D.diskPatch 0
        (D.overlapHomologyEquiv 0 z) = (D.oldHomologyEquiv 0 a, 0) := by
      dsimp [z]
      rw [LinearEquiv.apply_symm_apply]
      exact hc
    refine ⟨z, ?_, ?_⟩
    · rw [← D.coverLeft_old, hL, LinearEquiv.symm_apply_apply]
    · have hs := congrArg Prod.snd hL
      rw [leftHomologyMap_apply] at hs
      change singularHomologyMap _ 0 z = 0
      rw [singularHomologyMap_comp]
      exact neg_eq_zero.mp hs
  · rintro ⟨z, hza, hz⟩
    have hL : leftHomologyMap D.oldNeighborhood D.diskPatch 0
        (D.overlapHomologyEquiv 0 z) = (D.oldHomologyEquiv 0 a, 0) := by
      apply Prod.ext
      · exact (D.oldHomologyEquiv 0).symm_apply_eq.mp ((D.coverLeft_old 0 z).trans hza)
      · rw [leftHomologyMap_apply]
        rw [cellDiskBoundaryHomologyMap, singularHomologyMap_comp] at hz
        exact neg_eq_zero.mpr hz
    have hzero := LinearMap.congr_fun
      (leftHomologyMap_comp_right D.oldNeighborhood D.diskPatch 0) (D.overlapHomologyEquiv 0 z)
    change rightHomologyMap D.oldNeighborhood D.diskPatch 0
      (leftHomologyMap D.oldNeighborhood D.diskPatch 0 (D.overlapHomologyEquiv 0 z)) = 0 at hzero
    rw [hL, D.coverRight_old] at hzero
    exact hzero

theorem cell_oldHomologyMap_injective_of_attaching_component
    (p : D.old) (hcomponent : ∀ u, Joined (D.attachingSphere u) p) :
    Injective (D.oldHomologyMap 0) := by
  let c : C(D.diskPatch, D.old) := ContinuousMap.const _ p
  have heq : D.attachingHomologyMap 0 =
      (singularHomologyMap c 0).comp (cellDiskBoundaryHomologyMap D) := by
    apply homologyZero_linearMap_ext
    intro u
    change singularHomologyMap D.attachingSphere 0 (pointClass u) =
      singularHomologyMap c 0 (singularHomologyMap _ 0 (pointClass u))
    rw [singularHomologyMap_pointClass, singularHomologyMap_pointClass,
      singularHomologyMap_pointClass]
    exact (pointClass_eq_iff_joined _ _).mpr (hcomponent u)
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro a ha
  obtain ⟨z, hza, hz⟩ := (cell_oldHomologyMap_zero_iff D a).mp ha
  rw [← hza, heq, LinearMap.comp_apply, hz, map_zero]

theorem cell_old_pathConnected_of_attaching_component [PathConnectedSpace X]
    (p : D.old) (hcomponent : ∀ u, Joined (D.attachingSphere u) p) :
    PathConnectedSpace D.old := by
  let : Nonempty D.old := ⟨p⟩
  exact pathConnectedSpace_of_homologyZero_injective (subtypeInclusion D.old)
    (cell_oldHomologyMap_injective_of_attaching_component D p hcomponent)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
