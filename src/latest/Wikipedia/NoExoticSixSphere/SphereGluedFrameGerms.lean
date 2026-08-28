import Wikipedia.NoExoticSixSphere.SphereFrameGerms
import Wikipedia.NoExoticSixSphere.SphereGluedCapGerms

/-!
# Exact original frame operators on the glued sphere's open pieces

The proved equality of map germs transfers to the full original operator,
including its manifold normal columns and actual framed derivative. The
cap reparametrizations are retained; their derivatives are not discarded.
-/

noncomputable section

open Set Function Filter Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization SphereSumNeck

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)
  (ν : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (Φ : PartialDiffeomorph 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6)
    (Vector 3 × Vector 3) M ∞)
  (F G : Sphere 3 → M) {ε a : ℝ} (hε : 0 < ε) (ha : a ∈ Icc (0 : ℝ) 1)
  (hprod : closedBall (0 : Vector 3) (ε * 4) ×ˢ
    closedBall (0 : Vector 3) (ε * 4) ⊆ Φ.source)

include hε ha hprod in
theorem sphereFrameOperator_glued_north
    (hleft : ∀ v, (v, 0) ∈ Φ.source → Φ (v, 0) = F (sourceChart v))
    {x : Sphere 3} (hx : x ∈ northRegion) :
    e.sphereFrameOperator ν (gluedSphere Φ ε a F G) x =
      e.sphereFrameOperator ν (F ∘ sphereCap ε) x :=
  e.sphereFrameOperator_eq_of_germ ν
    (gluedSphere_eventuallyEq_north Φ F G hε ha hprod hleft hx)

include hε ha hprod in
theorem sphereFrameOperator_glued_south
    (hright : ∀ v, (0, v) ∈ Φ.source → Φ (0, v) = G (sourceChart v))
    {x : Sphere 3} (hx : x ∈ southRegion) :
    e.sphereFrameOperator ν (gluedSphere Φ ε a F G) x =
      e.sphereFrameOperator ν (G ∘ (sphereCap ε ∘ reflectHead)) x :=
  e.sphereFrameOperator_eq_of_germ ν
    (gluedSphere_eventuallyEq_south Φ F G hε ha hprod hright hx)

theorem sphereFrameOperator_glued_middle {x : Sphere 3} (hx : x ∈ neckRegion) :
    e.sphereFrameOperator ν (gluedSphere Φ ε a F G) x =
      e.sphereFrameOperator ν (middlePiece Φ ε a) x := by
  apply e.sphereFrameOperator_eq_of_germ ν
  filter_upwards [isOpen_neckRegion.mem_nhds hx] with y hy
  exact gluedSphere_middle Φ F G hy

end NoExoticSixSphere.EuclideanEmbedding
