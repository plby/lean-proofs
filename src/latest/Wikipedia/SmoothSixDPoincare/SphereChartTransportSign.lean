import Wikipedia.SmoothSixDPoincare.SphereChartTransportFrame
import Wikipedia.SmoothSixDPoincare.SphereLocalDegreeOrientation

/-!
# Outward chart signs under the constructed sphere motion

The exact radial-frame transport identity determines the actual coordinate
transition's determinant. A determinant-one ambient isometry therefore
preserves the outward sign convention, including when its two native charts
have different coordinate orientation signs.
-/

noncomputable section

open Set Metric
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.SpherePoint

open SphereNormalCoordinates

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {m : ℕ} [Fact (Module.finrank ℝ V = m + 1)]
  (x y : sphere (0 : V) 1) (R : V ≃ₗᵢ[ℝ] V) (he : sphereHomeomorph R x = y)

theorem chart_radial_frame_det (j : (ℝ × EuclideanSpace ℝ (Fin m)) ≃L[ℝ] V) :
    ((chartRadialFrame (NativeParametrization.centered y) 0).comp
        j.symm.toContinuousLinearMap).det *
      (NativeChartTransition.linear x y
        (sphereDiffeomorph (n := m) R) he).toLinearEquiv.toLinearMap.det =
    R.toLinearEquiv.toLinearMap.det *
      ((chartRadialFrame (NativeParametrization.centered x) 0).comp
        j.symm.toContinuousLinearMap).det := by
  let L := NativeChartTransition.linear x y (sphereDiffeomorph (n := m) R) he
  let Q := (ContinuousLinearMap.id ℝ ℝ).prodMap L.toContinuousLinearMap
  let T : V →L[ℝ] V := j.toContinuousLinearMap.comp (Q.comp j.symm.toContinuousLinearMap)
  have hdetT : T.det = L.toLinearEquiv.toLinearMap.det := by
    have hconj : T.det = Q.det := LinearMap.det_conj Q.toLinearMap j.toLinearEquiv
    rw [hconj]
    change (LinearMap.prodMap (LinearMap.id : ℝ →ₗ[ℝ] ℝ) L.toLinearEquiv.toLinearMap).det = _
    rw [LinearMap.det_prodMap, LinearMap.det_id, one_mul]
  have hfactor : ((chartRadialFrame (NativeParametrization.centered y) 0).comp
      j.symm.toContinuousLinearMap).comp T =
      R.toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((chartRadialFrame (NativeParametrization.centered x) 0).comp
          j.symm.toContinuousLinearMap) := by
    apply ContinuousLinearMap.ext
    intro v
    change chartRadialFrame (NativeParametrization.centered y) 0
      (j.symm (j (Q (j.symm v)))) =
        R (chartRadialFrame (NativeParametrization.centered x) 0 (j.symm v))
    rw [j.symm_apply_apply]
    exact congrArg (fun A : (ℝ × EuclideanSpace ℝ (Fin m)) →L[ℝ] V => A (j.symm v))
      (chart_radial_frame_comp x y R he)
  calc
    _ = (((chartRadialFrame (NativeParametrization.centered y) 0).comp
        j.symm.toContinuousLinearMap).comp T).det := by
      rw [hdetT.symm]
      exact (LinearMap.det_comp _ _).symm
    _ = _ := (congrArg ContinuousLinearMap.det hfactor).trans (LinearMap.det_comp _ _)

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem chartJacobian_transport
    (j : (ℝ × F) ≃L[ℝ] V) (B : EuclideanSpace ℝ (Fin m) ≃L[ℝ] F) :
    chartJacobian (NativeParametrization.centered y) j B 0 *
      (NativeChartTransition.linear x y
        (sphereDiffeomorph (n := m) R) he).toLinearEquiv.toLinearMap.det =
      R.toLinearEquiv.toLinearMap.det * chartJacobian (NativeParametrization.centered x) j B 0 :=
  chart_radial_frame_det x y R he
    ((ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ) B).trans j)

theorem chartJacobian_transport_sign
    (hR : R.toLinearEquiv.toLinearMap.det = 1)
    (j : (ℝ × F) ≃L[ℝ] V) (B : EuclideanSpace ℝ (Fin m) ≃L[ℝ] F) :
    SignType.sign (chartJacobian (NativeParametrization.centered y) j B 0) *
      SignType.sign
        (NativeChartTransition.linear x y
          (sphereDiffeomorph (n := m) R) he).toLinearEquiv.toLinearMap.det =
      SignType.sign (chartJacobian (NativeParametrization.centered x) j B 0) := by
  have h := chartJacobian_transport x y R he j B
  rw [hR, one_mul] at h
  rw [← sign_mul, h]

end Wikipedia.SmoothSixDPoincare.SpherePoint
