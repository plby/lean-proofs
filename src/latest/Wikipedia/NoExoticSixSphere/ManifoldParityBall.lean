import Wikipedia.NoExoticSixSphere.SphereTimeChart
import Wikipedia.NoExoticSixSphere.ManifoldChartLinkParity
import Wikipedia.NoExoticSixSphere.ManifoldAffineSingularities
import Wikipedia.NoExoticSixSphere.CompactChartRegion
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# Actual charted parity-one balls in the original parameter manifold

Each ball retains a genuine partial diffeomorphism containing the closed unit
ball. Its compact region is exactly the closure of its open region, and the
frontier is exactly its actual linking sphere. The center is its only intrinsic
singularity; the linking operators are the genuine spatial chart derivatives.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereFamily

open GLOrthonormalization ManifoldAffineSphereFamily Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]

structure ParityBall (g : ℝ → Sphere 3 → M) (q : ℝ × Sphere 3) where
  sourceChart : SourceChart
  targetChart : TargetChart 6 M
  chart : PartialDiffeomorph (𝓡 4) (𝓘(ℝ, ℝ).prod (𝓡 3))
    (Vector 4) (ℝ × Sphere 3) ∞
  ball_source : closedBall (0 : Vector 4) 1 ⊆ chart.source
  center : chart 0 = q
  chart_valid : ∀ z ∈ closedBall (0 : Vector 4) 1,
    (chart z).1 ∈ Ioo (0 : ℝ) 1 ∧ (chart z).2 ∈ sourceChart.source ∧
      g (chart z).1 (chart z).2 ∈ targetChart.source
  singular_iff : ∀ z ∈ closedBall (0 : Vector 4) 1,
    chart z ∈ singularParameters (n := 6) g ↔ z = 0
  link : C(Sphere 3, Monomorphism.Space 6 3)
  link_value : ∀ v, (link v).val = spatialInCharts g sourceChart targetChart (chart v.val)
  parity_one : Monomorphism.sphereParity 1 link = 1

namespace ParityBall

variable {g : ℝ → Sphere 3 → M} {q : ℝ × Sphere 3} (B : ParityBall g q)

def closedRegion : Set (ℝ × Sphere 3) := B.chart '' closedBall (0 : Vector 4) 1

def openRegion : Set (ℝ × Sphere 3) := B.chart '' ball (0 : Vector 4) 1

def boundaryRegion : Set (ℝ × Sphere 3) := B.chart '' sphere (0 : Vector 4) 1

theorem openRegion_subset_closedRegion : B.openRegion ⊆ B.closedRegion :=
  image_mono ball_subset_closedBall

theorem boundaryRegion_subset_closedRegion : B.boundaryRegion ⊆ B.closedRegion :=
  image_mono sphere_subset_closedBall

theorem closedRegion_subset_interiorTime :
    B.closedRegion ⊆ Ioo (0 : ℝ) 1 ×ˢ (univ : Set (Sphere 3)) := by
  rintro y ⟨z, hz, rfl⟩
  exact ⟨(B.chart_valid z hz).1, mem_univ _⟩

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

theorem center_mem_openRegion : q ∈ B.openRegion :=
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

theorem frontier_closedRegion : frontier B.closedRegion = B.boundaryRegion := by
  have he : B.closedRegion = CurveChart.region B.chart.toOpenPartialHomeomorph.symm
      (closedBall (0 : Vector 4) 1) :=
    (CurveChart.region_eq_image B.chart.toOpenPartialHomeomorph.symm B.ball_source).symm
  have hc : closure (closedBall (0 : Vector 4) 1) = closedBall (0 : Vector 4) 1 :=
    isClosed_closedBall.closure_eq
  rw [he, CurveChart.frontier_region _
    (hc.symm ▸ isCompact_closedBall (0 : Vector 4) 1)
    (hc.symm ▸ B.ball_source), frontier_closedBall _ one_ne_zero]
  rfl

theorem closedRegion_sdiff_openRegion : B.closedRegion \ B.openRegion = B.boundaryRegion := by
  rw [← B.frontier_openRegion, frontier, B.isOpen_openRegion.interior_eq, B.closure_openRegion]

include B in
theorem center_singular : q ∈ singularParameters (n := 6) g := by
  have h := (B.singular_iff 0 (mem_closedBall_self zero_le_one)).mpr rfl
  rwa [B.center] at h

theorem closedRegion_inter_singular :
    B.closedRegion ∩ singularParameters (n := 6) g = {q} := by
  ext y
  constructor
  · rintro ⟨⟨z, hz, rfl⟩, hsing⟩
    have hz0 := (B.singular_iff z hz).mp hsing
    rw [hz0]
    exact mem_singleton_iff.mpr B.center
  · rintro rfl
    exact ⟨⟨0, mem_closedBall_self zero_le_one, B.center⟩, B.center_singular⟩

theorem boundaryRegion_disjoint_singular :
    Disjoint B.boundaryRegion (singularParameters (n := 6) g) := by
  apply disjoint_left.mpr
  rintro y ⟨z, hz, rfl⟩ hsing
  have hz0 := (B.singular_iff z (sphere_subset_closedBall hz)).mp hsing
  simp [hz0] at hz

end ParityBall
end NoExoticSixSphere.SphereFamily
