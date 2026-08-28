import Wikipedia.NoExoticSixSphere.QuaternionicHopfChartNormalLift

/-!
# The original stereographic Hopf normal frame is the computed inverse

Compute the kernel and prove that the displayed right inverse is
orthogonal to it. Uniqueness identifies the ACTUAL canonical normal
frame of the chosen stereographic embedding, in its original fiber atlas.
-/

noncomputable section

open scoped Quaternion Manifold ContDiff

namespace NoExoticSixSphere.QuaternionicHopf

theorem southChartEquations_kernel (q : Sphere 3) (v : V 7) :
    fderiv ℝ southChartEquations ((2 : ℝ) • southChartUnit q) v = 0 ↔
      first (StereographicEquator.lift 7 v) = 0 ∧
        inner ℝ (southFiberPoint q).val (StereographicEquator.lift 7 v) = 0 := by
  rw [southChartEquations_derivative]
  constructor
  · intro h
    have he : (first (StereographicEquator.lift 7 v) +
        (inner ℝ (southFiberPoint q).val (StereographicEquator.lift 7 v)) • (1 : ℍ)) *
          star (second (southFiberPoint q).val) = 0 :=
      targetTailChartEquiv.injective (h.trans (map_zero targetTailChartEquiv).symm)
    have hb : star (second (southFiberPoint q).val) ≠ 0 := by
      intro hz
      have hh := south_second_mul_star (southFiberPoint q) (first_southFiberPoint q)
      rw [hz, mul_zero] at hh
      exact zero_ne_one hh
    have hs := (mul_eq_zero.mp he).resolve_right hb
    have hr : inner ℝ (southFiberPoint q).val (StereographicEquator.lift 7 v) = 0 := by
      have hh := congrArg (fun z : ℍ ↦ z.re) hs
      simpa only [Quaternion.re_add, Quaternion.re_smul, first_lift_re, Quaternion.re_one,
        zero_add, smul_eq_mul, mul_one, Quaternion.re_zero] using hh
    refine ⟨?_, hr⟩
    simpa only [hr, zero_smul, add_zero] using hs
  · rintro ⟨hf, hi⟩
    rw [hf, hi, zero_smul, add_zero, zero_mul, map_zero]

theorem chartNormalLift_mem_orthogonal (q : Sphere 3) (w : ℍ) :
    chartNormalLift q w ∈ (fderiv ℝ southChartEquations ((2 : ℝ) • southChartUnit q)).kerᗮ := by
  rw [Submodule.mem_orthogonal']
  intro v hv
  obtain ⟨hf, hi⟩ := (southChartEquations_kernel q v).mp hv
  have hs : inner ℝ (second (southFiberPoint q).val)
      (second (StereographicEquator.lift 7 v)) = 0 := by
    rw [inner_quaternion_coordinates, first_southFiberPoint, inner_zero_left, zero_add] at hi
    exact hi
  have hh := StereographicEquator.inner_lift 7 (chartNormalLift q w) v
  rw [lift_chartNormalLift] at hh
  rw [← hh, inner_quaternion_coordinates, hf, inner_zero_right, zero_add,
    second_chartNormalAmbient, real_inner_smul_left, hs, mul_zero]

theorem southChartEquations_orthogonalRightInverse (q : Sphere 3) :
    orthogonalRightInverse (fderiv ℝ southChartEquations ((2 : ℝ) • southChartUnit q)) =
      (chartNormalLift q).comp targetTailChartEquiv.symm.toContinuousLinearMap := by
  apply orthogonalRightInverse_eq_of_rightInverse _ (southChartEquations_surjective q)
  · exact chartNormalLift_coordinates_right_inverse q
  · rintro _ ⟨v, rfl⟩
    exact chartNormalLift_mem_orthogonal q (targetTailChartEquiv.symm v)

theorem southChartFrame_parametrized (q : Sphere 3) (v : V 4) :
    letI := regularFiberAtlas sphereMap contMDiff_sphereMap south south_regular 3
      (by simp only [finrank_euclideanSpace_fin]);
    southChartFrame.ambient (southFiberDiffeomorph q) v =
      chartNormalLift q (targetTailChartEquiv.symm v) := by
  let := regularFiberAtlas sphereMap contMDiff_sphereMap south south_regular 3
    (by simp only [finrank_euclideanSpace_fin])
  change (StereographicFiber.frame (k := 3) sphereMap contMDiff_sphereMap south south_regular
    (spherePole 7) pole_maps_antipode_south).ambient (southFiberDiffeomorph q) v = _
  rw [StereographicFiber.frame_ambient]
  change orthogonalRightInverse (fderiv ℝ southChartEquations
    (sphereProjection 7 (southFiberDiffeomorph q).val)) v = _
  rw [southFiberDiffeomorph_val, sourceChart_southFiber, southChartEquations_orthogonalRightInverse]
  rfl

theorem lift_southChartFrame_parametrized (q : Sphere 3) (v : V 4) :
    letI := regularFiberAtlas sphereMap contMDiff_sphereMap south south_regular 3
      (by simp only [finrank_euclideanSpace_fin]);
    StereographicEquator.lift 7 (southChartFrame.ambient (southFiberDiffeomorph q) v) =
      chartNormalAmbient q (targetTailChartEquiv.symm v) := by
  let := regularFiberAtlas sphereMap contMDiff_sphereMap south south_regular 3
    (by simp only [finrank_euclideanSpace_fin])
  rw [southChartFrame_parametrized, lift_chartNormalLift]

end NoExoticSixSphere.QuaternionicHopf
