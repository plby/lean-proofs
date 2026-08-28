import Wikipedia.SmoothSixDPoincare.CellCoverHomotopy
import Wikipedia.HopfProblem.SingularMayerVietoris
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCirclePoint

/-!
# Actual singular homology maps of the cell-attachment cover

The maps are induced by the original attaching sphere and old-space
inclusion. The connecting map is the genuine open-cover Mayer–Vietoris
map, transported through the constructed annular sphere equivalence.
-/

noncomputable section

open Set Metric Topology ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.EmbeddedCellAttachment

open Wikipedia.HopfProblem.SingularMayerVietoris
  Wikipedia.HopfProblem.PeriodTorusHigherHomology

variable {N X : Type} [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace X]
  (D : EmbeddedCellAttachment N X)

def oldHomologyEquiv (k : ℕ) :
    SingularHomology D.old k ≃ₗ[ℤ] SingularHomology D.oldNeighborhood k :=
  homotopyEquivHomologyEquiv D.oldHomotopyEquiv k

def overlapHomologyEquiv (k : ℕ) :
    SingularHomology (sphere (0 : N) 1) k ≃ₗ[ℤ]
      SingularHomology ↥(D.oldNeighborhood ∩ D.diskPatch) k :=
  homotopyEquivHomologyEquiv D.overlapSphereEquiv k

def attachingHomologyMap (k : ℕ) :
    SingularHomology (sphere (0 : N) 1) k →ₗ[ℤ] SingularHomology D.old k :=
  singularHomologyMap D.attachingSphere k

def oldHomologyMap (k : ℕ) : SingularHomology D.old k →ₗ[ℤ] SingularHomology X k :=
  singularHomologyMap (subtypeInclusion D.old) k

def cellConnectingMap (k : ℕ) :
    SingularHomology X (k + 1) →ₗ[ℤ] SingularHomology (sphere (0 : N) 1) k :=
  (D.overlapHomologyEquiv k).symm.toLinearMap.comp
    (connectingHomomorphism D.oldNeighborhood D.diskPatch
      D.isOpen_oldNeighborhood D.isOpen_diskPatch D.open_cover k)

theorem diskPatch_homology_subsingleton (k : ℕ) (hk : k ≠ 0) :
    Subsingleton (SingularHomology D.diskPatch k) := by
  let := D.diskPatch_contractible
  exact contractible_homology_subsingleton D.diskPatch k hk

/-- Retraction identifies the original overlap inclusion with the original attaching map. -/
theorem coverLeft_old (k : ℕ) (a : SingularHomology (sphere (0 : N) 1) k) :
    (D.oldHomologyEquiv k).symm
      (leftHomologyMap D.oldNeighborhood D.diskPatch k (D.overlapHomologyEquiv k a)).1 =
        D.attachingHomologyMap k a := by
  rw [leftHomologyMap_apply]
  change singularHomologyMap D.oldRetraction k
    (singularHomologyMap (ContinuousMap.inclusion inter_subset_left) k
      (singularHomologyMap D.overlapSphereEquiv.toFun k a)) =
    singularHomologyMap D.attachingSphere k a
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp,
    ← LinearMap.comp_apply, ← singularHomologyMap_comp]
  change singularHomologyMap (D.overlapOldMap.comp D.overlapSphereEquiv.toFun) k a = _
  rw [D.overlapOldMap_comp_sphere]

theorem coverRight_old (k : ℕ) (a : SingularHomology D.old k) :
    rightHomologyMap D.oldNeighborhood D.diskPatch k (D.oldHomologyEquiv k a, 0) =
      D.oldHomologyMap k a := by
  rw [rightHomologyMap_apply, map_zero, add_zero]
  change singularHomologyMap (subtypeInclusion D.oldNeighborhood) k
    (singularHomologyMap D.oldInclusion k a) = singularHomologyMap (subtypeInclusion D.old) k a
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp]
  rfl

theorem coverLeft_formula (k : ℕ) (hk : k ≠ 0)
    (a : SingularHomology (sphere (0 : N) 1) k) :
    leftHomologyMap D.oldNeighborhood D.diskPatch k (D.overlapHomologyEquiv k a) =
      (D.oldHomologyEquiv k (D.attachingHomologyMap k a), 0) := by
  let := D.diskPatch_homology_subsingleton k hk
  apply Prod.ext
  · exact (D.oldHomologyEquiv k).symm_apply_eq.mp (D.coverLeft_old k a)
  · exact Subsingleton.elim _ _

theorem coverRight_formula (k : ℕ) (hk : k ≠ 0)
    (b : SingularHomology D.oldNeighborhood k × SingularHomology D.diskPatch k) :
    rightHomologyMap D.oldNeighborhood D.diskPatch k b =
      D.oldHomologyMap k ((D.oldHomologyEquiv k).symm b.1) := by
  let := D.diskPatch_homology_subsingleton k hk
  have hb : (D.oldHomologyEquiv k ((D.oldHomologyEquiv k).symm b.1), 0) = b :=
    Prod.ext ((D.oldHomologyEquiv k).apply_symm_apply b.1) (Subsingleton.elim _ _)
  calc
    _ = rightHomologyMap D.oldNeighborhood D.diskPatch k
        (D.oldHomologyEquiv k ((D.oldHomologyEquiv k).symm b.1), 0) :=
      congrArg (rightHomologyMap D.oldNeighborhood D.diskPatch k) hb.symm
    _ = _ := D.coverRight_old k _

theorem cellConnecting_eq_zero_iff (k : ℕ) (a : SingularHomology X (k + 1)) :
    D.cellConnectingMap k a = 0 ↔
      connectingHomomorphism D.oldNeighborhood D.diskPatch
        D.isOpen_oldNeighborhood D.isOpen_diskPatch D.open_cover k a = 0 := by
  change (D.overlapHomologyEquiv k).symm _ = 0 ↔ _ = 0
  constructor
  · intro h
    exact (D.overlapHomologyEquiv k).symm.injective (h.trans (map_zero _).symm)
  · intro h
    rw [h, map_zero]

end Wikipedia.SmoothSixDPoincare.EmbeddedCellAttachment
