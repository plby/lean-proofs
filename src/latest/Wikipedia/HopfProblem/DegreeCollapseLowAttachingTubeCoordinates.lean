import Wikipedia.HopfProblem.DegreeCollapseLowAttachingLocalization
import Wikipedia.NoExoticSixSphere.InjectiveLocalDiffeomorph

/-!

# Actual smooth coordinates on the entire low-dimensional attaching tube

The original closed tube is injective and locally diffeomorphic in the native
atlas. Its open transverse interior is one genuine partial diffeomorphism
onto the actual open image in the original manifold. Its map is the original
tube, not an independently chosen coordinate identification.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct

open NoExoticSixSphere GLOrthonormalization Stiefel

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel}
  {f : NoExoticSixSphere.Sphere d → M}
  (A : FramedAttachingProduct e a f)

def openTubeDomain : Set (NoExoticSixSphere.Sphere d × Vector (7 - d)) :=
  univ ×ˢ ball (0 : Vector (7 - d)) A.radius

theorem isOpen_openTubeDomain : IsOpen A.openTubeDomain := isOpen_univ.prod isOpen_ball

theorem injOn_tube_openTubeDomain : InjOn A.tube A.openTubeDomain := by
  intro p hp q hq he
  let p' : NoExoticSixSphere.Sphere d × closedBall (0 : Vector (7 - d)) A.radius :=
    (p.1, ⟨p.2, ball_subset_closedBall hp.2⟩)
  let q' : NoExoticSixSphere.Sphere d × closedBall (0 : Vector (7 - d)) A.radius :=
    (q.1, ⟨q.2, ball_subset_closedBall hq.2⟩)
  have hpq : p' = q' := A.tube_embedded.injective he
  exact congrArg
    (fun z : NoExoticSixSphere.Sphere d × closedBall (0 : Vector (7 - d)) A.radius ↦
      (z.1, z.2.val)) hpq

theorem isLocalDiffeomorphOn_tube_openTubeDomain :
    IsLocalDiffeomorphOn ((𝓡 d).prod (𝓡 (7 - d))) (𝓡 7) ∞ A.tube A.openTubeDomain :=
  fun p ↦ A.tube_localDiffeomorph p.val.1 p.val.2 (ball_subset_closedBall p.property.2)

def tubeCoordinates : PartialDiffeomorph ((𝓡 d).prod (𝓡 (7 - d))) (𝓡 7)
    (NoExoticSixSphere.Sphere d × Vector (7 - d)) M ∞ := by
  letI : Nonempty (NoExoticSixSphere.Sphere d × Vector (7 - d)) := ⟨(spherePole d, 0)⟩
  exact injectiveLocalPartialDiffeomorph A.isOpen_openTubeDomain A.injOn_tube_openTubeDomain
    A.isLocalDiffeomorphOn_tube_openTubeDomain

theorem tubeCoordinates_apply (p : NoExoticSixSphere.Sphere d × Vector (7 - d)) :
    A.tubeCoordinates p = A.tube p := rfl

theorem tubeCoordinates_source : A.tubeCoordinates.source = A.openTubeDomain := rfl

theorem tubeCoordinates_target : A.tubeCoordinates.target = A.tube '' A.openTubeDomain := rfl

theorem halfTube_mem_source (s : NoExoticSixSphere.Sphere d) {v : Vector (7 - d)}
    (hv : v ∈ closedBall (0 : Vector (7 - d)) (A.radius / 2)) :
    (s, v) ∈ A.tubeCoordinates.source :=
  ⟨mem_univ s, (closedBall_subset_ball (half_lt_self A.radius_pos)) hv⟩

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct
