import Wikipedia.HopfProblem.DegreeCollapseLowClosedCapCoordinates

/-!

# A continuous actual closed cap through the rounded collar

Glue the original handle map on a smaller closed disk to the actual collar
sheet on the complementary closed annulus. The two ambient formulas agree
at the cut. The resulting map has exactly the original tube as its outer
face, with the same sphere parameters and transverse radius.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.SurgeryPair

open NoExoticSixSphere GLOrthonormalization Stiefel RoundedTrace
open Wikipedia.SmoothSixDPoincare.PuncturedHandle

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  [CompactSpace M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel}
  {f : NoExoticSixSphere.Sphere d → M} (A : FramedAttachingProduct e a f)

def capInner (p : CapDomain d) : Vector (e.ambientDimension + (1 + (1 + (d + 1)))) :=
  A.map (capDisk A p, p.2.val)

def capOuter (p : CapDomain d) : Vector (e.ambientDimension + (1 + (1 + (d + 1)))) :=
  A.collarSheet (capCollar A p)

def capPoint (p : CapDomain d) : Vector (e.ambientDimension + (1 + (1 + (d + 1)))) :=
  if ‖capDisk A p‖ ≤ cutRadius A then capInner A p else capOuter A p

omit [CompactSpace M] in
theorem capTransverse_mem (hR : A.radius = 2) (p : CapDomain d) :
    p.2.val ∈ closedBall (0 : Vector (7 - d)) A.radius := by
  rw [mem_closedBall, dist_zero_right, mem_sphere_zero_iff_norm.mp p.2.property, hR]
  norm_num

theorem capDisk_mem_inner (p : CapDomain d) (hp : ‖capDisk A p‖ ≤ cutRadius A) :
    capDisk A p ∈ closedBall (0 : Vector (d + 1)) 1 := by
  rw [mem_closedBall, dist_zero_right]
  exact hp.trans (cutRadius_lt_one A).le

theorem capInner_eq_outer_of_cut (hR : A.radius = 2) (p : CapDomain d)
    (hp : ‖capDisk A p‖ = cutRadius A) : capInner A p = capOuter A p := by
  have hx := capDisk_mem_inner A p hp.le
  have hi : A.innerRadius ≤ ‖capDisk A p‖ := by
    rw [hp]
    exact (innerRadius_lt_cutRadius A).le
  rw [capOuter, capCollar_of_cut A p hp]
  exact A.map_eq_cylinder_collarCoordinates hx hi (capTransverse_mem A hR p)

theorem continuousOn_capInner (hR : A.radius = 2) :
    ContinuousOn (capInner A) {p | ‖capDisk A p‖ ≤ cutRadius A} := by
  intro p hp
  have hc := (A.smooth (capDisk A p) (capDisk_mem_inner A p hp)
    p.2.val (capTransverse_mem A hR p)).continuousAt
  have hparam : Continuous (fun q : CapDomain d ↦ (capDisk A q, q.2.val)) :=
    (continuous_capDisk A).prodMk (continuous_subtype_val.comp continuous_snd)
  have hmap : ContinuousAt (A.map ∘ fun q : CapDomain d ↦ (capDisk A q, q.2.val)) p :=
    hc.comp (f := fun q : CapDomain d ↦ (capDisk A q, q.2.val)) hparam.continuousAt
  exact hmap.continuousWithinAt

theorem continuousOn_capOuter (hR : A.radius = 2) :
    ContinuousOn (capOuter A) {p | cutRadius A ≤ ‖capDisk A p‖} :=
  A.contMDiffOn_collarSheet.continuousOn.comp (continuousOn_capCollar A)
    (fun p hp ↦ collarParameters_subset_source A (capCollar_mem A hR p hp))

theorem continuous_capPoint (hR : A.radius = 2) : Continuous (capPoint A) :=
  continuous_if_le (continuous_capDisk A).norm continuous_const
    (continuousOn_capInner A hR) (continuousOn_capOuter A hR)
      (capInner_eq_outer_of_cut A hR)

theorem capPoint_of_inner (p : CapDomain d) (hp : ‖capDisk A p‖ ≤ cutRadius A) :
    capPoint A p = capInner A p := if_pos hp

theorem capPoint_of_outer (hR : A.radius = 2) (p : CapDomain d)
    (hp : cutRadius A ≤ ‖capDisk A p‖) : capPoint A p = capOuter A p := by
  by_cases hi : ‖capDisk A p‖ ≤ cutRadius A
  · rw [capPoint_of_inner A p hi]
    exact capInner_eq_outer_of_cut A hR p (le_antisymm hi hp)
  · exact if_neg hi

theorem capPoint_newBoundary (hR : A.radius = 2) (s : NoExoticSixSphere.Sphere d)
    (w : sphere (0 : Vector (7 - d)) 1) :
    capPoint A (newBoundary (s, w)) =
      (LowHeightCylinder.heightCylinder d e) (A.tube (s, oldRadius A • w.val), 0) := by
  have hp : cutRadius A ≤ ‖capDisk A (newBoundary (s, w))‖ := by
    rw [capDisk_norm]
    change cutRadius A ≤ oldRadius A * ‖s.val‖
    rw [ClosedHemisphere.unit_norm, mul_one]
    exact (cutRadius_lt_one A).le.trans (oldRadius_gt_one A hR).le
  rw [capPoint_of_outer A hR _ hp, capOuter, capCollar_newBoundary A hR]
  rfl

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.SurgeryPair
