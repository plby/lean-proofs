import Wikipedia.NoExoticSixSphere.SmoothFramedTube
import Wikipedia.NoExoticSixSphere.SmoothCollapseCoordinates
import Wikipedia.NoExoticSixSphere.RadialCompressionDerivative

/-!
# The collapse differential on the specified normal frame

For a compressed framed tube of radius `r`, the derivative in the normal
direction is `r` times the original frame. The inverse collapse coordinate
sends this positively rescaled frame to the identity.
-/

open scoped Manifold ContDiff
open Set

namespace NoExoticSixSphere.EuclideanEmbedding

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  (e : EuclideanEmbedding n M)
  (a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel)
  (r : ℝ) (hr : 0 < r)
  (Φ : PartialDiffeomorph ((𝓡 n).prod 𝓘(ℝ, e.NormalModel)) (𝓡 e.ambientDimension)
    (M × e.NormalModel) (EuclideanSpace ℝ (Fin e.ambientDimension)) ∞)
  (hsource : Φ.source = univ)
  (hformula : ∀ p, Φ p = e.toFun p.1 +
    a.ambient p.1 (OpenPartialHomeomorph.univBall (0 : e.NormalModel) r p.2))

include hr hformula in
theorem hasFDerivAt_framedTube_fiber (x : M) :
    HasFDerivAt (fun v : e.NormalModel ↦ Φ (x, v)) (r • a.ambient x) 0 := by
  have hf : (fun v : e.NormalModel ↦ Φ (x, v)) =
      (fun v ↦ e.toFun x +
        a.ambient x (OpenPartialHomeomorph.univBall (0 : e.NormalModel) r v)) :=
    funext (fun v ↦ hformula (x, v))
  rw [hf]
  have hd := ((a.ambient x).hasFDerivAt.comp 0 (hasFDerivAt_univBall_zero r hr)).const_add
    (e.toFun x)
  simpa using hd

include hformula in
theorem framedTube_zero (x : M) : Φ (x, 0) = e.toFun x := by
  rw [hformula, OpenPartialHomeomorph.univBall_apply_zero, map_zero, add_zero]

include hr hsource hformula in
theorem fderiv_collapseCoordinate_comp_frame (x : M) :
    (fderiv ℝ (SmoothCollapseCoordinates.coordinate Φ) (e.toFun x)).comp
      (r • a.ambient x) = ContinuousLinearMap.id ℝ e.NormalModel := by
  have hz := e.framedTube_zero a r Φ hformula x
  have hmem : Φ (x, 0) ∈ Φ.target := Φ.map_source' (by rw [hsource]; trivial)
  have hd := (SmoothCollapseCoordinates.contMDiffAt_coordinate Φ hmem).contDiffAt
    |>.differentiableAt (by simp)
  have hc := hd.hasFDerivAt.comp 0 (e.hasFDerivAt_framedTube_fiber a r hr Φ hformula x)
  rw [hz] at hc
  have heq : (fun v : e.NormalModel ↦ SmoothCollapseCoordinates.coordinate Φ (Φ (x, v))) =
      id := by
    funext v
    exact SmoothCollapseCoordinates.coordinate_apply Φ (by rw [hsource]; trivial)
  change HasFDerivAt (fun v : e.NormalModel ↦ SmoothCollapseCoordinates.coordinate Φ (Φ (x, v)))
    ((fderiv ℝ (SmoothCollapseCoordinates.coordinate Φ) (e.toFun x)).comp (r • a.ambient x)) 0 at hc
  rw [heq] at hc
  exact hc.unique (hasFDerivAt_id (0 : e.NormalModel))

include hr hsource hformula in
theorem fderiv_collapseCoordinate_frame (x : M) (v : e.NormalModel) :
    fderiv ℝ (SmoothCollapseCoordinates.coordinate Φ) (e.toFun x)
      (r • a.ambient x v) = v := by
  have h := congrArg (fun L : e.NormalModel →L[ℝ] e.NormalModel ↦ L v)
    (e.fderiv_collapseCoordinate_comp_frame a r hr Φ hsource hformula x)
  exact h

end NoExoticSixSphere.EuclideanEmbedding
