import Wikipedia.NoExoticSixSphere.FourDiskParityBallSystem

/-!
# The actual disk with its native singularity balls removed

The complement has its original topology and contains no native singularity.
Its frontier is exactly the original outer sphere together with the actual
linking spheres. The latter and the outer sphere are retained as continuous
maps into this compact regular domain. No homology relation is assumed here.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.GenericFourDisk.ParityBallSystem

open GLOrthonormalization DiskDoublePoints

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  {g : Vector 4 → M} (P : ParityBallSystem g)

def puncturedDisk : Set (Vector 4) := closedBall 0 1 \ P.openHoles

theorem isCompact_puncturedDisk : IsCompact P.puncturedDisk :=
  (isCompact_closedBall (0 : Vector 4) 1).diff P.isOpen_openHoles

theorem injective_mfderiv_on_puncturedDisk (x : Vector 4) (hx : x ∈ P.puncturedDisk) :
    Injective (mfderiv (𝓡 4) (𝓡 7) g x) := by
  by_contra hs
  exact hx.2 (P.singular_subset_openHoles ⟨hx.1, hs⟩)

theorem interior_puncturedDisk : interior P.puncturedDisk = Metric.ball 0 1 \ P.closedHoles := by
  rw [puncturedDisk, sdiff_eq, interior_inter, interior_closedBall _ one_ne_zero,
    interior_compl, P.closure_openHoles]
  rfl

theorem frontier_puncturedDisk : frontier P.puncturedDisk = sphere 0 1 ∪ P.linkingBoundary := by
  have hball : closedBall (0 : Vector 4) 1 \ Metric.ball 0 1 = sphere 0 1 := by
    ext x
    simp only [mem_sdiff, mem_closedBall_zero_iff, mem_ball_zero_iff, mem_sphere_zero_iff_norm]
    exact ⟨fun h ↦ le_antisymm h.1 (le_of_not_gt h.2),
      fun h ↦ ⟨h.le, not_lt.mpr h.ge⟩⟩
  rw [P.isCompact_puncturedDisk.isClosed.frontier_eq, P.interior_puncturedDisk,
    puncturedDisk, ← hball, ← P.closedHoles_sdiff_openHoles]
  ext x
  have hCI : x ∈ P.closedHoles → x ∈ Metric.ball 0 1 :=
    fun hx ↦ P.closedHoles_subset_interior hx
  have hIA : x ∈ Metric.ball (0 : Vector 4) 1 → x ∈ closedBall 0 1 :=
    fun hx ↦ ball_subset_closedBall hx
  have hUC : x ∈ P.openHoles → x ∈ P.closedHoles := fun hx ↦ P.openHoles_subset_closedHoles hx
  simp only [mem_sdiff, mem_union]
  tauto

theorem linkingBoundary_subset_puncturedDisk : P.linkingBoundary ⊆ P.puncturedDisk := by
  rw [← P.closedHoles_sdiff_openHoles]
  intro x hx
  exact ⟨ball_subset_closedBall (P.closedHoles_subset_interior hx.1), hx.2⟩

theorem boundary_mem_puncturedDisk (x : Vector 4) (hx : x ∈ sphere 0 1) :
    x ∈ P.puncturedDisk := by
  apply P.isCompact_puncturedDisk.isClosed.frontier_subset
  rw [P.frontier_puncturedDisk]
  exact Or.inl hx

theorem boundary_disjoint_linkingBoundary : Disjoint (sphere 0 1) P.linkingBoundary := by
  apply disjoint_left.mpr
  intro x hx hlink
  rw [← P.closedHoles_sdiff_openHoles] at hlink
  have hnorm := mem_ball_zero_iff.mp (P.closedHoles_subset_interior hlink.1)
  exact (mem_sphere_zero_iff_norm.mp hx).not_lt hnorm

def outerBoundary : C(Sphere 3, P.puncturedDisk) where
  toFun s := ⟨s.val, P.boundary_mem_puncturedDisk s.val s.property⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

def linkingSphere (x : singularSet g) : C(Sphere 3, P.puncturedDisk) where
  toFun s := ⟨(P.ball x).chart s.val,
    P.linkingBoundary_subset_puncturedDisk (mem_iUnion.mpr ⟨x, ⟨s.val, s.property, rfl⟩⟩)⟩
  continuous_toFun :=
    ((P.ball x).chart.contMDiffOn_toFun.continuousOn.mono
      (sphere_subset_closedBall.trans (P.ball x).ball_source)).domRestrict.subtype_mk _

end NoExoticSixSphere.GenericFourDisk.ParityBallSystem
