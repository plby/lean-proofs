import Wikipedia.SmoothSixDPoincare.CellAttachmentHomologyOne

/-!
# Connected cell boundaries preserve the actual degree-zero homology

The original old-space inclusion is injective and surjective in degree zero
when the attaching sphere is path connected. The proof uses the actual
Mayer--Vietoris maps, and permits a disconnected old space.
-/

noncomputable section

open Set Metric Function Topology ContinuousMap

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open Wikipedia.SmoothSixDPoincare
  SingularMayerVietoris PeriodTorusHigherHomology SphereHomology

variable {N X : Type} [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace X]
  (D : EmbeddedCellAttachment N X) [PathConnectedSpace (sphere (0 : N) 1)]

theorem cell_oldHomologyMap_zero_injective : Injective (D.oldHomologyMap 0) := by
  let : ContractibleSpace D.diskPatch := D.diskPatch_contractible
  let q : C(sphere (0 : N) 1, D.diskPatch) :=
    (ContinuousMap.inclusion inter_subset_right).comp D.overlapSphereEquiv.toFun
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro a ha
  have hpair : (D.oldHomologyEquiv 0 a, 0) ∈
      LinearMap.ker (rightHomologyMap D.oldNeighborhood D.diskPatch 0) := by
    change rightHomologyMap D.oldNeighborhood D.diskPatch 0
      (D.oldHomologyEquiv 0 a, 0) = 0
    rw [D.coverRight_old]
    exact ha
  rw [← exact_at_pair D.oldNeighborhood D.diskPatch
    D.isOpen_oldNeighborhood D.isOpen_diskPatch D.open_cover 0] at hpair
  obtain ⟨c, hc⟩ := hpair
  have hq : singularHomologyMap q 0 ((D.overlapHomologyEquiv 0).symm c) = 0 := by
    have h := congrArg Prod.snd hc
    rw [leftHomologyMap_apply] at h
    rw [singularHomologyMap_comp]
    change singularHomologyMap (ContinuousMap.inclusion inter_subset_right) 0
      (D.overlapHomologyEquiv 0 ((D.overlapHomologyEquiv 0).symm c)) = 0
    rw [LinearEquiv.apply_symm_apply]
    exact neg_eq_zero.mp h
  have hz : (D.overlapHomologyEquiv 0).symm c = 0 :=
    singularHomologyMap_zero_injective q (hq.trans (map_zero _).symm)
  have hc0 : c = 0 := by
    apply (D.overlapHomologyEquiv 0).symm.injective
    exact hz.trans (map_zero _).symm
  rw [hc0, map_zero] at hc
  apply (D.oldHomologyEquiv 0).injective
  exact (congrArg Prod.fst hc).symm.trans (map_zero _).symm

theorem cell_oldHomologyMap_zero_surjective : Surjective (D.oldHomologyMap 0) := by
  let : ContractibleSpace D.diskPatch := D.diskPatch_contractible
  let q : C(sphere (0 : N) 1, D.diskPatch) :=
    (ContinuousMap.inclusion inter_subset_right).comp D.overlapSphereEquiv.toFun
  intro a
  obtain ⟨⟨b, c⟩, hbc⟩ := rightHomologyMap_zero_surjective D.oldNeighborhood D.diskPatch
    D.isOpen_oldNeighborhood D.isOpen_diskPatch D.open_cover a
  obtain ⟨z, hz⟩ := singularHomologyMap_zero_surjective q c
  let v := D.overlapHomologyEquiv 0 z
  have hv : singularHomologyMap (ContinuousMap.inclusion inter_subset_right) 0 v = c := by
    rw [singularHomologyMap_comp] at hz
    exact hz
  have hzero := LinearMap.congr_fun
    (leftHomologyMap_comp_right D.oldNeighborhood D.diskPatch 0) v
  change rightHomologyMap D.oldNeighborhood D.diskPatch 0
    (leftHomologyMap D.oldNeighborhood D.diskPatch 0 v) = 0 at hzero
  rw [leftHomologyMap_apply, rightHomologyMap_apply, map_neg, hv] at hzero
  have hrel : singularHomologyMap (subtypeInclusion D.oldNeighborhood) 0
      (singularHomologyMap (ContinuousMap.inclusion inter_subset_left) 0 v) =
      singularHomologyMap (subtypeInclusion D.diskPatch) 0 c := by
    apply sub_eq_zero.mp
    simpa only [sub_eq_add_neg] using hzero
  refine ⟨(D.oldHomologyEquiv 0).symm
    (b + singularHomologyMap (ContinuousMap.inclusion inter_subset_left) 0 v), ?_⟩
  rw [← D.coverRight_old, LinearEquiv.apply_symm_apply,
    rightHomologyMap_apply, map_zero, add_zero, map_add, hrel]
  exact hbc

theorem cell_oldHomologyMap_zero_bijective : Bijective (D.oldHomologyMap 0) :=
  ⟨cell_oldHomologyMap_zero_injective D, cell_oldHomologyMap_zero_surjective D⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
