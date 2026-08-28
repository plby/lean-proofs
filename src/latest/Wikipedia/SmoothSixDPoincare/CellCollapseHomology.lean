import Wikipedia.SmoothSixDPoincare.CellCollapseCoverMap
import Wikipedia.SmoothSixDPoincare.OnePointCollapseHomology
import Wikipedia.SmoothSixDPoincare.CellAttachmentHomologySequence

/-!
# The actual collapse-induced map is the original cell connecting map

Naturality of the genuine open-cover sequence and the exact overlap-sphere
formula identify the original collapse map on homology. No degree/count
formula, arbitrary homology marking, or replacement attaching map is used.
-/

noncomputable section

open Set Metric Topology ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.EmbeddedCellAttachment

open Wikipedia.HopfProblem.SingularMayerVietoris
  Wikipedia.HopfProblem.PeriodTorusHigherHomology

variable {N X : Type} [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace X]
  (D : EmbeddedCellAttachment N X)

theorem collapse_overlapHomology_compare (k : ℕ)
    (a : SingularHomology (sphere (0 : N) 1) k) :
    singularHomologyMap D.collapseOverlapMap k (D.overlapHomologyEquiv k a) =
      OnePointCover.overlapHomologyEquiv OnePointCover.overlapRadius
        OnePointCover.overlapRadius_pos k a := by
  change singularHomologyMap D.collapseOverlapMap k
    (singularHomologyMap D.overlapSphereEquiv.toFun k a) =
      singularHomologyMap _ k a
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp, D.collapseOverlap_comp_sphere]

/-- The original cell connecting map is the original collapse-induced homology map. -/
theorem collapse_connecting_compare (k : ℕ) (a : SingularHomology X (k + 1)) :
    OnePointCover.sphereConnecting OnePointCover.overlapRadius
      OnePointCover.overlapRadius_pos k (singularHomologyMap D.collapseMap (k + 1) a) =
        D.cellConnectingMap k a := by
  apply (OnePointCover.overlapHomologyEquiv (N := N) OnePointCover.overlapRadius
    OnePointCover.overlapRadius_pos k).injective
  change OnePointCover.overlapHomologyEquiv _ _ k
      ((OnePointCover.overlapHomologyEquiv _ _ k).symm _) =
    OnePointCover.overlapHomologyEquiv _ _ k ((D.overlapHomologyEquiv k).symm _)
  rw [LinearEquiv.apply_symm_apply, ← D.collapse_overlapHomology_compare,
    LinearEquiv.apply_symm_apply]
  exact (CoverNaturality.connecting_naturality_apply
    D.oldNeighborhood D.diskPatch OnePointCover.oldPatch OnePointCover.finitePatch
    D.collapseMap D.collapseMaps_oldNeighborhood D.collapseMaps_diskPatch
    D.isOpen_oldNeighborhood D.isOpen_diskPatch D.open_cover
    OnePointCover.oldPatch_open OnePointCover.finitePatch_open OnePointCover.cover k a).symm

variable [FiniteDimensional ℝ N]

theorem collapse_homology_equiv_compare (k : ℕ) (a : SingularHomology X (k + 2)) :
    OnePointCover.sphereHomologyEquiv OnePointCover.overlapRadius
      OnePointCover.overlapRadius_pos k (singularHomologyMap D.collapseMap (k + 2) a) =
        D.cellConnectingMap (k + 1) a :=
  D.collapse_connecting_compare (k + 1) a

/-- The collapse kills exactly the homology classes coming from the actual old space. -/
theorem collapse_homology_kernel (k : ℕ) :
    LinearMap.ker (singularHomologyMap D.collapseMap (k + 1)) =
      LinearMap.range (D.oldHomologyMap (k + 1)) := by
  rw [D.cell_exact_at_ambient]
  ext a
  change singularHomologyMap D.collapseMap (k + 1) a = 0 ↔ D.cellConnectingMap k a = 0
  rw [← D.collapse_connecting_compare]
  constructor
  · intro h
    rw [h, map_zero]
  · intro h
    exact (OnePointCover.sphereConnecting_injective (N := N) OnePointCover.overlapRadius
      OnePointCover.overlapRadius_pos k) (h.trans (map_zero _).symm)

end Wikipedia.SmoothSixDPoincare.EmbeddedCellAttachment
