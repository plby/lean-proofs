import Wikipedia.NoExoticSixSphere.QuaternionicHopfSourceChart

/-!
# The literal target stereographic coordinates and the quaternion tail

The target coordinate map is constructed from the original pole-complement
orthonormal coordinates. Its inverse is the quaternion tail of the lifted
coordinate vector. Both inverse identities are proved explicitly.
-/

noncomputable section

open scoped Quaternion Manifold ContDiff

namespace NoExoticSixSphere.QuaternionicHopf

def targetTailAxis : ℍ →L[ℝ] V 5 :=
  (SphereCylinder.join 3).toContinuousLinearMap.comp
    ((0 : ℍ →L[ℝ] ℝ).prod Quaternion.linearIsometryEquivTuple.toContinuousLinearMap)

theorem targetTailAxis_apply (w : ℍ) :
    targetTailAxis w = SphereCylinder.join 3 (0, Quaternion.linearIsometryEquivTuple w) := rfl

theorem targetTailAxis_orthogonal (w : ℍ) :
    inner ℝ (spherePole 4).val (targetTailAxis w) = 0 := by
  rw [pole_inner_head]
  rfl

theorem tailQuaternion_targetTailAxis (w : ℍ) : tailQuaternion (targetTailAxis w) = w := by
  rw [targetTailAxis_apply, tailQuaternion_join]

def targetTailChart : ℍ →L[ℝ] V 4 := (StereographicEquator.project 4).comp targetTailAxis

def chartTailQuaternion : V 4 →L[ℝ] ℍ := tailQuaternion.comp (StereographicEquator.liftL 4)

theorem chartTailQuaternion_targetTailChart (w : ℍ) :
    chartTailQuaternion (targetTailChart w) = w := by
  change tailQuaternion (StereographicEquator.lift 4
    (StereographicEquator.project 4 (targetTailAxis w))) = w
  rw [StereographicEquator.lift_project_of_orthogonal 4 _ (targetTailAxis_orthogonal w),
    tailQuaternion_targetTailAxis]

theorem targetTailAxis_chartTailQuaternion (v : V 4) :
    targetTailAxis (chartTailQuaternion v) = StereographicEquator.lift 4 v := by
  have hz : (StereographicEquator.lift 4 v) 0 = 0 := by
    rw [← pole_inner_head, real_inner_comm]
    exact StereographicEquator.inner_lift_pole 4 v
  rw [targetTailAxis_apply]
  change SphereCylinder.join 3 (0, Quaternion.linearIsometryEquivTuple
    (Quaternion.linearIsometryEquivTuple.symm
      (SphereCylinder.tail 3 (StereographicEquator.lift 4 v)))) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact join_zero_tail _ hz

theorem targetTailChart_chartTailQuaternion (v : V 4) :
    targetTailChart (chartTailQuaternion v) = v := by
  change StereographicEquator.project 4 (targetTailAxis (chartTailQuaternion v)) = v
  rw [targetTailAxis_chartTailQuaternion, StereographicEquator.project_lift]

def targetTailChartEquiv : ℍ ≃L[ℝ] V 4 :=
  ContinuousLinearEquiv.equivOfInverse targetTailChart chartTailQuaternion
    chartTailQuaternion_targetTailChart targetTailChart_chartTailQuaternion

theorem targetTailChartEquiv_apply (w : ℍ) : targetTailChartEquiv w = targetTailChart w := rfl

theorem targetTailChartEquiv_symm_apply (v : V 4) :
    targetTailChartEquiv.symm v = chartTailQuaternion v := rfl

theorem project_target_join (t : ℝ) (w : ℍ) :
    StereographicEquator.project 4 (SphereCylinder.join 3
      (t, Quaternion.linearIsometryEquivTuple w)) = targetTailChart w := by
  have he : SphereCylinder.join 3 (t, Quaternion.linearIsometryEquivTuple w) =
      t • (spherePole 4).val + targetTailAxis w := by
    rw [targetTailAxis_apply, ← pole_join]
    rw [← map_smul, ← map_add]
    congr 1
    simp
  rw [he, map_add, map_smul, StereographicEquator.project_pole, smul_zero, zero_add]
  rfl

end NoExoticSixSphere.QuaternionicHopf
