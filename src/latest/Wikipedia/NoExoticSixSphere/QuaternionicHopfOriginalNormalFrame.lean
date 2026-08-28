import Wikipedia.NoExoticSixSphere.QuaternionicHopfModelRadialDerivative
import Wikipedia.NoExoticSixSphere.OrthogonalRightInverseCoordinates

/-!
# Exact comparison with the original sphere-fiber normal frame

The existing model-chart and radial-extension construction has the
computed quaternionic south-fiber frame, precomposed by one fixed target
coordinate equivalence. Both the actual regular-fiber atlas and the
original ambient inclusion are retained.
-/

noncomputable section

open scoped Quaternion Manifold ContDiff

namespace NoExoticSixSphere.QuaternionicHopf

theorem originalEquations_derivative (a x : Sphere 7) (hx : sphereMap x = south) :
    fderiv ℝ (SphereFiberNormalFrame.equations sphereMap south a) x.val =
      augmentedTargetChange.toContinuousLinearMap.comp
        (fderiv ℝ (radialSouthEquations a) x.val) := by
  have hf : first x.val = 0 := (sphereMap_eq_south_iff x).mp hx
  have h₁ := (hasStrictFDerivAt_norm_sq x.val).hasFDerivAt.sub_const 1
  have h₂ := ((contDiffAt_modelRadialTail a x hx).differentiableAt (by simp)).hasFDerivAt
  rw [modelRadialTail_derivative a x hx] at h₂
  have h := (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (V 4)).symm.hasFDerivAt.comp x.val
    (h₁.prodMk h₂)
  change HasFDerivAt (𝕜 := ℝ) (SphereFiberNormalFrame.equations sphereMap south a) _ x.val at h
  apply ContinuousLinearMap.ext
  intro v
  rw [h.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    smul_apply, innerSL_apply_apply, nsmul_eq_mul, Nat.cast_ofNat]
  change WithLp.toLp 2 (2 * inner ℝ x.val v,
    southTargetChange (fderiv ℝ (radialTailExtension a) x.val v)) =
      augmentedTargetChange (fderiv ℝ (radialSouthEquations a) x.val v)
  rw [radialTailExtension_derivative a x hf, radialSouthEquations_derivative a x hf,
    southNormalEquations_fderiv x.val hf]
  simp only [ContinuousLinearMap.comp_apply]
  rw [polynomial_fderiv_south x.val hf, tailQuaternion_join, augmentedTargetChange_apply]

theorem originalEquations_orthogonalRightInverse (a x : Sphere 7) (hx : sphereMap x = south) :
    orthogonalRightInverse (fderiv ℝ (SphereFiberNormalFrame.equations sphereMap south a) x.val) =
      (southNormalLift (second x.val)).comp augmentedTargetChange.symm.toContinuousLinearMap := by
  have hf : first x.val = 0 := (sphereMap_eq_south_iff x).mp hx
  have hr : Function.Surjective (fderiv ℝ (radialSouthEquations a) x.val) := by
    rw [radialSouthEquations_derivative a x hf]
    exact southNormalEquations_surjective x hf
  rw [originalEquations_derivative a x hx,
    orthogonalRightInverse_target_coordinates _ hr,
    radialSouthEquations_orthogonalRightInverse a x hf]

theorem original_southNormalFrame_ambient (a : Sphere 7)
    (x : {x : Sphere 7 // sphereMap x = south}) :
    letI := regularFiberAtlas sphereMap contMDiff_sphereMap south south_regular 3
      (by simp only [finrank_euclideanSpace_fin]);
    (SphereFiberNormalFrame.normalFrame sphereMap contMDiff_sphereMap south south_regular
      3 (by decide) a).ambient x =
      (southNormalLift (second x.val.val)).comp
        augmentedTargetChange.symm.toContinuousLinearMap := by
  let := regularFiberAtlas sphereMap contMDiff_sphereMap south south_regular 3
    (by simp only [finrank_euclideanSpace_fin])
  rw [SphereFiberNormalFrame.normalFrame_ambient]
  exact originalEquations_orthogonalRightInverse a x.val x.property

theorem original_southNormalFrame_parametrized (a : Sphere 7) (q : Sphere 3) :
    letI := regularFiberAtlas sphereMap contMDiff_sphereMap south south_regular 3
      (by simp only [finrank_euclideanSpace_fin]);
    (SphereFiberNormalFrame.normalFrame sphereMap contMDiff_sphereMap south south_regular
      3 (by decide) a).ambient (southFiberDiffeomorph q) =
      (southNormalFrame.ambient q).comp augmentedTargetChange.symm.toContinuousLinearMap := by
  let := regularFiberAtlas sphereMap contMDiff_sphereMap south south_regular 3
    (by simp only [finrank_euclideanSpace_fin])
  rw [original_southNormalFrame_ambient, southFiberDiffeomorph_val, southNormalFrame_ambient]

theorem original_southNormalFrame_transverse (a : Sphere 7) (q : Sphere 3) (w : ℍ) :
    letI := regularFiberAtlas sphereMap contMDiff_sphereMap south south_regular 3
      (by simp only [finrank_euclideanSpace_fin]);
    (SphereFiberNormalFrame.normalFrame sphereMap contMDiff_sphereMap south south_regular
      3 (by decide) a).ambient (southFiberDiffeomorph q)
        (augmentedTargetChange (WithLp.toLp 2 (0, (2 : ℝ) • w))) =
      firstAxis (w * Quaternion.linearIsometryEquivTuple.symm q.val) := by
  let := regularFiberAtlas sphereMap contMDiff_sphereMap south south_regular 3
    (by simp only [finrank_euclideanSpace_fin])
  rw [original_southNormalFrame_parametrized]
  change southNormalFrame.ambient q (augmentedTargetChange.symm
    (augmentedTargetChange (WithLp.toLp 2 (0, (2 : ℝ) • w)))) = _
  rw [ContinuousLinearEquiv.symm_apply_apply, southNormalFrame_transverse]

theorem southNormalFrame_radial (q : Sphere 3) :
    southNormalFrame.ambient q (WithLp.toLp 2 (2, (0 : ℍ))) = southFiberAmbient q := by
  apply first_second_ext
  · rw [southNormalFrame_first]
    change (1 / 2 : ℝ) • ((0 : ℍ) * Quaternion.linearIsometryEquivTuple.symm q.val) =
      first (southFiberPoint q).val
    rw [zero_mul, smul_zero, first_southFiberPoint]
  · rw [southNormalFrame_second]
    change (1 / 2 : ℝ) • ((2 : ℝ) • Quaternion.linearIsometryEquivTuple.symm q.val) =
      second (southFiberPoint q).val
    rw [second_southFiberPoint, smul_smul]
    norm_num only
    exact one_smul ℝ _

theorem original_southNormalFrame_radial (a : Sphere 7) (q : Sphere 3) :
    letI := regularFiberAtlas sphereMap contMDiff_sphereMap south south_regular 3
      (by simp only [finrank_euclideanSpace_fin]);
    (SphereFiberNormalFrame.normalFrame sphereMap contMDiff_sphereMap south south_regular
      3 (by decide) a).ambient (southFiberDiffeomorph q)
        (WithLp.toLp 2 (2, (0 : V 4))) = southFiberAmbient q := by
  let := regularFiberAtlas sphereMap contMDiff_sphereMap south south_regular 3
    (by simp only [finrank_euclideanSpace_fin])
  rw [original_southNormalFrame_parametrized]
  change southNormalFrame.ambient q (augmentedTargetChange.symm
    (WithLp.toLp 2 (2, (0 : V 4)))) = _
  rw [augmentedTargetChange_symm_apply, map_zero]
  exact southNormalFrame_radial q

end NoExoticSixSphere.QuaternionicHopf
