import Wikipedia.HopfProblem.DegreeCollapseSevenAttachingLocalization
import Wikipedia.NoExoticSixSphere.InjectiveLocalDiffeomorph

/-!
# Smooth coordinates on the entire original attaching tube

The constructed closed tube is injective and locally diffeomorphic. Its open
transverse interior therefore gives one genuine smooth partial diffeomorphism
onto an open subset of the original manifold, with the actual tube as its map.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct

open NoExoticSixSphere GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

def openTubeDomain : Set (Sphere 3 × Vector 4) := univ ×ˢ ball (0 : Vector 4) A.radius

theorem isOpen_openTubeDomain : IsOpen A.openTubeDomain := isOpen_univ.prod isOpen_ball

theorem injOn_tube_openTubeDomain : InjOn A.tube A.openTubeDomain := by
  intro p hp q hq he
  let p' : Sphere 3 × closedBall (0 : Vector 4) A.radius :=
    (p.1, ⟨p.2, ball_subset_closedBall hp.2⟩)
  let q' : Sphere 3 × closedBall (0 : Vector 4) A.radius :=
    (q.1, ⟨q.2, ball_subset_closedBall hq.2⟩)
  have hpq : p' = q' := A.tube_embedded.injective he
  exact congrArg (fun z : Sphere 3 × closedBall (0 : Vector 4) A.radius ↦ (z.1, z.2.val)) hpq

theorem isLocalDiffeomorphOn_tube_openTubeDomain :
    IsLocalDiffeomorphOn ((𝓡 3).prod (𝓡 4)) (𝓡 7) ∞ A.tube A.openTubeDomain :=
  fun p ↦ A.tube_localDiffeomorph p.val.1 p.val.2 (ball_subset_closedBall p.property.2)

def tubeCoordinates : PartialDiffeomorph ((𝓡 3).prod (𝓡 4)) (𝓡 7)
    (Sphere 3 × Vector 4) M ∞ := by
  letI : Nonempty (Sphere 3 × Vector 4) := ⟨(pole 3, 0)⟩
  exact injectiveLocalPartialDiffeomorph A.isOpen_openTubeDomain A.injOn_tube_openTubeDomain
    A.isLocalDiffeomorphOn_tube_openTubeDomain

theorem tubeCoordinates_apply (p : Sphere 3 × Vector 4) : A.tubeCoordinates p = A.tube p := rfl

theorem tubeCoordinates_source : A.tubeCoordinates.source = A.openTubeDomain := rfl

theorem tubeCoordinates_target : A.tubeCoordinates.target = A.tube '' A.openTubeDomain := rfl

theorem halfTube_mem_source (s : Sphere 3) {v : Vector 4}
    (hv : v ∈ closedBall (0 : Vector 4) (A.radius / 2)) :
    (s, v) ∈ A.tubeCoordinates.source :=
  ⟨mem_univ s, (closedBall_subset_ball (half_lt_self A.radius_pos)) hv⟩

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct
