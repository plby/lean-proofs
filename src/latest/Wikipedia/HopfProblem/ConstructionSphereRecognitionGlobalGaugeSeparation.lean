import Wikipedia.HopfProblem.ConstructionSphereRecognitionGlobalGaugeSupport
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCuspGeometry

/-!
# Separation of the original filling patches and elliptic supports

The actual chosen base discs are pairwise disjoint.  Their full inverse
images in the original threefold therefore separate the two elliptic
patches from each other and from the entire original cusp patch.  The
closed elliptic supports inherit the same separation.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.GlobalGauge

open Elliptic SpecialPeriods SpecialPeriods.Threefold

/-- Distinct original elliptic patches are full preimages of disjoint chosen base discs. -/
theorem ellipticPatches_disjoint (j k : Kind) (hjk : j ≠ k) :
    Disjoint (Threefold.liftedPatch (some (some j)) : Set Threefold.Space)
      (Threefold.liftedPatch (some (some k)) : Set Threefold.Space) := by
  apply Set.disjoint_left.mpr
  intro y hy hk
  exact Set.disjoint_left.mp
    (specialBaseCover.fillingPatch_disjoint (fun h => hjk (Option.some.inj h))) hy hk

/-- The entire actual cusp patch is disjoint from either original elliptic patch. -/
theorem cuspPatch_disjoint_elliptic (j : Kind) :
    Disjoint (Threefold.liftedPatch (some none) : Set Threefold.Space)
      (Threefold.liftedPatch (some (some j)) : Set Threefold.Space) := by
  apply Set.disjoint_left.mpr
  intro y hy hj
  exact Set.disjoint_left.mp
    (specialBaseCover.fillingPatch_disjoint (show (none : Puncture) ≠ some j by simp)) hy hj

/-- The native cusp inclusion lands in precisely its original full gluing patch. -/
theorem cusp_inclusion_mem_patch (y : CuspGeometry.LocalSpace) :
    CuspGeometry.inclusion y ∈ (Threefold.liftedPatch (some none) : Set Threefold.Space) := by
  change CuspGeometry.inclusion y ∈ Threefold.projection ⁻¹'
    (specialBaseCover.fillingPatch none : Set TriangleCompactifiedOrbitSpace)
  rw [← CuspGeometry.inclusion_range]
  exact ⟨y, rfl⟩

/-- The native elliptic inclusion lands in its own unchanged full gluing patch. -/
theorem elliptic_inclusion_mem_patch (j : Kind) (y : EllipticGeometry.LocalSpace j) :
    EllipticGeometry.inclusion j y ∈
      (Threefold.liftedPatch (some (some j)) : Set Threefold.Space) := by
  change EllipticGeometry.inclusion j y ∈ Threefold.projection ⁻¹'
    (specialBaseCover.fillingPatch (some j) : Set TriangleCompactifiedOrbitSpace)
  rw [← EllipticGeometry.inclusion_range]
  exact ⟨y, rfl⟩

/-- Every point of the whole original cusp piece misses the elliptic patch. -/
theorem cusp_inclusion_not_mem_ellipticPatch (j : Kind) (y : CuspGeometry.LocalSpace) :
    CuspGeometry.inclusion y ∉
      (Threefold.liftedPatch (some (some j)) : Set Threefold.Space) :=
  Set.disjoint_left.mp (cuspPatch_disjoint_elliptic j) (cusp_inclusion_mem_patch y)

/-- The other original elliptic piece misses the selected elliptic patch pointwise. -/
theorem other_elliptic_inclusion_not_mem_patch (j k : Kind) (hjk : j ≠ k)
    (y : EllipticGeometry.LocalSpace k) :
    EllipticGeometry.inclusion k y ∉
      (Threefold.liftedPatch (some (some j)) : Set Threefold.Space) :=
  Set.disjoint_left.mp (ellipticPatches_disjoint k j hjk.symm)
    (elliptic_inclusion_mem_patch k y)

theorem ellipticSupports_disjoint (j k : Kind) (hjk : j ≠ k) :
    Disjoint (ellipticSupport j) (ellipticSupport k) :=
  (ellipticPatches_disjoint j k hjk).mono
    (ellipticSupport_subset_patch j) (ellipticSupport_subset_patch k)

theorem cuspPatch_disjoint_ellipticSupport (j : Kind) :
    Disjoint (Threefold.liftedPatch (some none) : Set Threefold.Space) (ellipticSupport j) :=
  (cuspPatch_disjoint_elliptic j).mono_right (ellipticSupport_subset_patch j)

/-- In particular no point of the original cusp piece is in an elliptic support. -/
theorem cusp_inclusion_not_mem_support (j : Kind) (y : CuspGeometry.LocalSpace) :
    CuspGeometry.inclusion y ∉ ellipticSupport j := by
  intro hy
  exact cusp_inclusion_not_mem_ellipticPatch j y (ellipticSupport_subset_patch j hy)

/-- The whole other original elliptic piece also misses the support. -/
theorem other_elliptic_inclusion_not_mem_support (j k : Kind) (hjk : j ≠ k)
    (y : EllipticGeometry.LocalSpace k) :
    EllipticGeometry.inclusion k y ∉ ellipticSupport j := by
  intro hy
  exact other_elliptic_inclusion_not_mem_patch j k hjk y (ellipticSupport_subset_patch j hy)

end Wikipedia.HopfProblem.ConstructionSphereRecognition.GlobalGauge
