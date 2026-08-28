import Wikipedia.NoExoticSixSphere.FourSevenLocalContribution
import Wikipedia.NoExoticSixSphere.FourDiskSingularities
import Wikipedia.NoExoticSixSphere.CompactChartRegion

/-!
# Actual parity-one balls in a specified source region

A retained partial diffeomorphism contains the full closed unit ball. Its
image stays in the specified source region and in one original target chart.
The center is its only native singularity; the linking operators are the
actual chart derivatives and have parity one. The region defaults to the
open unit disk, preserving the disk constructions while also allowing
the original annulus as a source region.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.GenericFourDisk

open GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]

structure ParityBall (g : Vector 4 → M) (x : Vector 4)
    (U : Set (Vector 4) := ball 0 1) where
  targetChart : PartialDiffeomorph (𝓡 7) (𝓡 7) M (Vector 7) ∞
  chart : PartialDiffeomorph (𝓡 4) (𝓡 4) (Vector 4) (Vector 4) ∞
  ball_source : closedBall (0 : Vector 4) 1 ⊆ chart.source
  center : chart 0 = x
  chart_valid : ∀ z ∈ closedBall (0 : Vector 4) 1,
    chart z ∈ U ∧ g (chart z) ∈ targetChart.source
  singular_iff : ∀ z ∈ closedBall (0 : Vector 4) 1,
    ¬ Injective (mfderiv (𝓡 4) (𝓡 7) g (chart z)) ↔ z = 0
  link : C(Sphere 3, Monomorphism.Space 7 4)
  link_value : ∀ v, (link v).val = fderiv ℝ (targetChart ∘ g) (chart v.val)
  parity_one : Monomorphism.sphereParity 2 link = 1

namespace ParityBall

variable {g : Vector 4 → M} {x : Vector 4} {U : Set (Vector 4)} (B : ParityBall g x U)

def closedRegion : Set (Vector 4) := B.chart '' closedBall (0 : Vector 4) 1

def openRegion : Set (Vector 4) := B.chart '' ball (0 : Vector 4) 1

def boundaryRegion : Set (Vector 4) := B.chart '' sphere (0 : Vector 4) 1

theorem openRegion_subset_closedRegion : B.openRegion ⊆ B.closedRegion :=
  image_mono ball_subset_closedBall

theorem boundaryRegion_subset_closedRegion : B.boundaryRegion ⊆ B.closedRegion :=
  image_mono sphere_subset_closedBall

theorem closedRegion_subset_interior : B.closedRegion ⊆ U := by
  rintro y ⟨z, hz, rfl⟩
  exact (B.chart_valid z hz).1

theorem isClosedEmbedding_chart :
    IsClosedEmbedding (fun z : closedBall (0 : Vector 4) 1 ↦ B.chart z.val) := by
  have hc := (B.chart.contMDiffOn_toFun.continuousOn.mono B.ball_source).domRestrict
  apply hc.isClosedEmbedding
  intro z w he
  exact Subtype.ext (B.chart.injOn (B.ball_source z.property) (B.ball_source w.property) he)

theorem isCompact_closedRegion : IsCompact B.closedRegion :=
  (isCompact_closedBall (0 : Vector 4) 1).image_of_continuousOn
    (B.chart.contMDiffOn_toFun.continuousOn.mono B.ball_source)

theorem openRegion_eq_region :
    B.openRegion = CurveChart.region B.chart.toOpenPartialHomeomorph.symm
      (ball (0 : Vector 4) 1) :=
  (CurveChart.region_eq_image B.chart.toOpenPartialHomeomorph.symm
    (ball_subset_closedBall.trans B.ball_source)).symm

theorem isOpen_openRegion : IsOpen B.openRegion := by
  rw [B.openRegion_eq_region]
  exact CurveChart.isOpen_region _ isOpen_ball

theorem center_mem_openRegion : x ∈ B.openRegion :=
  ⟨0, mem_ball_self zero_lt_one, B.center⟩

theorem closure_openRegion : closure B.openRegion = B.closedRegion := by
  have he : closure (ball (0 : Vector 4) 1) = closedBall (0 : Vector 4) 1 :=
    closure_ball _ one_ne_zero
  rw [B.openRegion_eq_region, CurveChart.closure_region _
    (he.symm ▸ isCompact_closedBall (0 : Vector 4) 1) (he.symm ▸ B.ball_source), he]
  rfl

theorem frontier_openRegion : frontier B.openRegion = B.boundaryRegion := by
  have he : closure (ball (0 : Vector 4) 1) = closedBall (0 : Vector 4) 1 :=
    closure_ball _ one_ne_zero
  rw [B.openRegion_eq_region, CurveChart.frontier_region _
    (he.symm ▸ isCompact_closedBall (0 : Vector 4) 1) (he.symm ▸ B.ball_source),
    frontier_ball _ one_ne_zero]
  rfl

theorem closedRegion_sdiff_openRegion : B.closedRegion \ B.openRegion = B.boundaryRegion := by
  rw [← B.frontier_openRegion, frontier, B.isOpen_openRegion.interior_eq, B.closure_openRegion]

include B in
theorem center_singular : ¬ Injective (mfderiv (𝓡 4) (𝓡 7) g x) := by
  have h := (B.singular_iff 0 (mem_closedBall_self zero_le_one)).mpr rfl
  rwa [B.center] at h

theorem closedRegion_inter_singular :
    B.closedRegion ∩ {y | ¬ Injective (mfderiv (𝓡 4) (𝓡 7) g y)} = {x} := by
  ext y
  constructor
  · rintro ⟨⟨z, hz, rfl⟩, hs⟩
    have hz0 := (B.singular_iff z hz).mp hs
    rw [hz0]
    exact mem_singleton_iff.mpr B.center
  · rintro rfl
    exact ⟨⟨0, mem_closedBall_self zero_le_one, B.center⟩, B.center_singular⟩

theorem boundaryRegion_disjoint_singular :
    Disjoint B.boundaryRegion {y | ¬ Injective (mfderiv (𝓡 4) (𝓡 7) g y)} := by
  apply disjoint_left.mpr
  rintro y ⟨z, hz, rfl⟩ hs
  have hz0 := (B.singular_iff z (sphere_subset_closedBall hz)).mp hs
  simp [hz0] at hz

end ParityBall
end NoExoticSixSphere.GenericFourDisk
