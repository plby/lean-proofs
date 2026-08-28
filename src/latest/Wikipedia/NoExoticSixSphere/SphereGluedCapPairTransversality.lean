import Wikipedia.NoExoticSixSphere.SphereNativeDerivativeCoordinates
import Wikipedia.NoExoticSixSphere.SphereGluedCapGerms

/-! # Native transversality at the three types of exterior-cap coincidence -/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (Φ : PartialDiffeomorph 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6)
    (Vector 3 × Vector 3) M ∞)
  (F G : Sphere 3 → M) {ε a : ℝ} (hε : 0 < ε) (ha : a ∈ Icc (0 : ℝ) 1)
  (hprod : closedBall (0 : Vector 3) (ε * 4) ×ˢ
    closedBall (0 : Vector 3) (ε * 4) ⊆ Φ.source)
  (hleft : ∀ v, (v, 0) ∈ Φ.source → Φ (v, 0) = F (sourceChart v))
  (hright : ∀ v, (0, v) ∈ Φ.source → Φ (0, v) = G (sourceChart v))

include hε ha hprod hleft in
theorem transverse_glued_north_pair (hF : ContMDiff (𝓡 3) (𝓡 6) ∞ F)
    (htF : NativeSphereSelfTransverse F)
    {x y : Sphere 3} (hx : x ∈ northRegion) (hy : y ∈ northRegion) (hne : x ≠ y)
    (he : gluedSphere Φ ε a F G x = gluedSphere Φ ε a F G y) :
    NativeSphereTransverseAt (gluedSphere Φ ε a F G) (gluedSphere Φ ε a F G) x y := by
  have Hx := gluedSphere_eventuallyEq_north Φ F G hε ha hprod hleft hx
  have Hy := gluedSphere_eventuallyEq_north Φ F G hε ha hprod hleft hy
  have hv : F (sphereCap ε x) = F (sphereCap ε y) :=
    Hx.eq_of_nhds.symm.trans (he.trans Hy.eq_of_nhds)
  have hd : sphereCap ε x ≠ sphereCap ε y :=
    fun h ↦ hne (northCap_injOn hε.ne' hx hy h)
  exact nativeSphereTransverseAt_of_local_reparametrizations (gluedSphere Φ ε a F G) F F
    (sphereCap ε) (sphereCap ε) x y hF hF
    (isLocalDiffeomorphAt_sphereCap hε.ne' (northRegion_head_pos hx))
    (isLocalDiffeomorphAt_sphereCap hε.ne' (northRegion_head_pos hy)) Hx Hy
    (htF (sphereCap ε x) (sphereCap ε y) hd hv)

include hε ha hprod hright in
theorem transverse_glued_south_pair (hG : ContMDiff (𝓡 3) (𝓡 6) ∞ G)
    (htG : NativeSphereSelfTransverse G)
    {x y : Sphere 3} (hx : x ∈ southRegion) (hy : y ∈ southRegion) (hne : x ≠ y)
    (he : gluedSphere Φ ε a F G x = gluedSphere Φ ε a F G y) :
    NativeSphereTransverseAt (gluedSphere Φ ε a F G) (gluedSphere Φ ε a F G) x y := by
  have Hx := gluedSphere_eventuallyEq_south Φ F G hε ha hprod hright hx
  have Hy := gluedSphere_eventuallyEq_south Φ F G hε ha hprod hright hy
  have hv : G (sphereCap ε (reflectHead x)) = G (sphereCap ε (reflectHead y)) :=
    Hx.eq_of_nhds.symm.trans (he.trans Hy.eq_of_nhds)
  have hd : sphereCap ε (reflectHead x) ≠ sphereCap ε (reflectHead y) :=
    fun h ↦ hne (southCap_injOn hε.ne' hx hy h)
  exact nativeSphereTransverseAt_of_local_reparametrizations (gluedSphere Φ ε a F G) G G
    (sphereCap ε ∘ reflectHead) (sphereCap ε ∘ reflectHead) x y hG hG
    (isLocalDiffeomorphAt_southCap hε.ne' hx) (isLocalDiffeomorphAt_southCap hε.ne' hy) Hx Hy
    (htG (sphereCap ε (reflectHead x)) (sphereCap ε (reflectHead y)) hd hv)

include hε ha hprod hleft hright in
theorem transverse_glued_mixed_pair
    (hF : ContMDiff (𝓡 3) (𝓡 6) ∞ F) (hG : ContMDiff (𝓡 3) (𝓡 6) ∞ G)
    (htFG : NativeSpherePairTransverse F G)
    {x y : Sphere 3} (hx : x ∈ northRegion) (hy : y ∈ southRegion)
    (he : gluedSphere Φ ε a F G x = gluedSphere Φ ε a F G y) :
    NativeSphereTransverseAt (gluedSphere Φ ε a F G) (gluedSphere Φ ε a F G) x y := by
  have Hx := gluedSphere_eventuallyEq_north Φ F G hε ha hprod hleft hx
  have Hy := gluedSphere_eventuallyEq_south Φ F G hε ha hprod hright hy
  have hv : F (sphereCap ε x) = G (sphereCap ε (reflectHead y)) :=
    Hx.eq_of_nhds.symm.trans (he.trans Hy.eq_of_nhds)
  exact nativeSphereTransverseAt_of_local_reparametrizations (gluedSphere Φ ε a F G) F G
    (sphereCap ε) (sphereCap ε ∘ reflectHead) x y hF hG
    (isLocalDiffeomorphAt_sphereCap hε.ne' (northRegion_head_pos hx))
    (isLocalDiffeomorphAt_southCap hε.ne' hy) Hx Hy
    (htFG (sphereCap ε x) (sphereCap ε (reflectHead y)) hv)

end NoExoticSixSphere.SphereSumNeck
