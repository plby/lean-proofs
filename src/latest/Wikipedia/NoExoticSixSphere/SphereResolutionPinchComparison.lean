import Wikipedia.NoExoticSixSphere.SphereLinearCollapseHemispheres
import Wikipedia.NoExoticSixSphere.SpherePinchTailReflection
import Wikipedia.NoExoticSixSphere.SpherePinchMap

/-!
# The actual immersed resolution is homotopic to an explicit sphere pinch

The northern input is precomposed with the constructed cap-to-pinch
homeomorphism. The southern input includes the additional tail reflection.
These reparametrizations are part of the theorem, not silently identified
with the identity. The two maps agree at the actual collapsed pole.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] (F G : C(Sphere 3, M)) (ε : ℝ) (hε : ε ≠ 0)

def northPinchInput : C(Sphere 3, M) :=
  F.comp ⟨capPinchComparison ε hε, (capPinchComparison ε hε).continuous⟩

def southPinchInput : C(Sphere 3, M) :=
  G.comp ⟨fun x ↦ capPinchComparison ε hε (tailReflection x),
    (capPinchComparison ε hε).continuous.comp contMDiff_tailReflection.continuous⟩

theorem pinchInput_base (hzero : F (sourceChart 0) = G (sourceChart 0)) :
    northPinchInput F ε hε (antipode pinchPole) =
      southPinchInput G ε hε (antipode pinchPole) := by
  change F (capPinchComparison ε hε (antipode pinchPole)) =
    G (capPinchComparison ε hε (tailReflection (antipode pinchPole)))
  rw [tailReflection_base, capPinchComparison_base, hzero]

def comparisonPinch (hzero : F (sourceChart 0) = G (sourceChart 0)) : C(Sphere 3, M) :=
  SphereFold.pinch pinchPole (northPinchInput F ε hε) (southPinchInput G ε hε)
    (pinchInput_base F G ε hε hzero)

variable [ChartedSpace (Vector 6) M]
  (Φ : PartialDiffeomorph 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6)
    (Vector 3 × Vector 3) M ∞)
  {ε} (hpos : 0 < ε)
  (hprod : closedBall (0 : Vector 3) (ε * 4) ×ˢ
    closedBall (0 : Vector 3) (ε * 4) ⊆ Φ.source)
  (hleft : ∀ v, (v, 0) ∈ Φ.source → Φ (v, 0) = F (sourceChart v))
  (hright : ∀ v, (0, v) ∈ Φ.source → Φ (0, v) = G (sourceChart v))

include hpos hprod hleft hright in
theorem linearSphere_eq_comparisonPinch (hzero : F (sourceChart 0) = G (sourceChart 0))
    (x : Sphere 3) :
    linearSphere Φ F G ε x = comparisonPinch F G ε hpos.ne' hzero x := by
  rcases lt_trichotomy (x.val 0) 0 with hx | hx | hx
  · rw [linearSphere_south Φ F G hpos hprod hright hx]
    have hs : SphereFold.height pinchPole x ≤ 0 := by rw [pinchPole_height]; exact hx.le
    rw [comparisonPinch, SphereFold.pinch_south _ _ _ _ x hs]
    change G (sphereCap ε (reflectHead x)) =
      G (capPinchComparison ε hpos.ne' (tailReflection (SphereFold.fold pinchPole x)))
    rw [capPinchComparison_fold_south ε hpos.ne' hx]
  · rw [linearSphere_equator_value Φ F G hpos hprod hleft hx]
    have he : SphereFold.height pinchPole x = 0 := by rwa [pinchPole_height]
    rw [comparisonPinch, SphereFold.pinch_equator _ _ _ _ x he]
    change F (sourceChart 0) = F (capPinchComparison ε hpos.ne' (antipode pinchPole))
    rw [capPinchComparison_base]
  · rw [linearSphere_north Φ F G hpos hprod hleft hx]
    have hn : 0 ≤ SphereFold.height pinchPole x := by rw [pinchPole_height]; exact hx.le
    rw [comparisonPinch, SphereFold.pinch_north _ _ _ _ x hn]
    change F (sphereCap ε x) = F (capPinchComparison ε hpos.ne' (SphereFold.fold pinchPole x))
    rw [capPinchComparison_fold_north ε hpos.ne' hx]

def immersedToPinchHomotopy (hF : ContMDiff (𝓡 3) (𝓡 6) ∞ F)
    (hG : ContMDiff (𝓡 3) (𝓡 6) ∞ G)
    (hzero : F (sourceChart 0) = G (sourceChart 0)) :
    (gluedSphereMap Φ F G hpos (show (1 : ℝ) ∈ Icc 0 1 by norm_num)
      hprod hleft hright hF hG).Homotopy
    (comparisonPinch F G ε hpos.ne' hzero) := by
  have he : linearSphereMap Φ F G hpos hprod hleft hright hF hG =
      comparisonPinch F G ε hpos.ne' hzero := by
    apply ContinuousMap.ext
    exact linearSphere_eq_comparisonPinch F G Φ hpos hprod hleft hright hzero
  rw [← he]
  exact immersedToLinearHomotopy Φ F G hpos hprod hleft hright hF hG

end NoExoticSixSphere.SphereSumNeck
