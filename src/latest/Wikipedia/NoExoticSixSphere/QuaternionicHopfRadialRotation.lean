import Wikipedia.NoExoticSixSphere.QuaternionicHopfChartNormalFrame
import Wikipedia.NoExoticSixSphere.OrthogonalRotations

/-!
# Exact radial-plane comparison of the two computed Hopf frames

The quarter turn sends the fixed source pole to the fiber radius and
the fiber radius to the negative pole. The resulting formula retains
the fixed reflection in the added normal coordinate and the factor two.
-/

noncomputable section

open scoped Quaternion Manifold ContDiff

namespace NoExoticSixSphere.QuaternionicHopf

def southQuarterTurn (q : Sphere 3) : V 8 ≃ₗᵢ[ℝ] V 8 :=
  localRotationEquiv (spherePole 7).val (southFiberPoint q).val

theorem southQuarterTurn_formula (q : Sphere 3) (v : V 8) :
    southQuarterTurn q v =
      v - (inner ℝ (spherePole 7).val v + inner ℝ (southFiberPoint q).val v) •
          (spherePole 7).val +
        (inner ℝ (spherePole 7).val v - inner ℝ (southFiberPoint q).val v) •
          (southFiberPoint q).val := by
  have hp : ‖(spherePole 7).val‖ = 1 := mem_sphere_zero_iff_norm.mp (spherePole 7).property
  have hx : ‖(southFiberPoint q).val‖ = 1 :=
    mem_sphere_zero_iff_norm.mp (southFiberPoint q).property
  have hpx := southFiber_orthogonal_sourcePole q
  have hxp : inner ℝ (southFiberPoint q).val (spherePole 7).val = 0 := by
    rw [real_inner_comm]
    exact hpx
  have hsum : ‖(spherePole 7).val + (southFiberPoint q).val‖ ^ 2 = 2 := by
    rw [norm_add_sq_real, hp, hx, hpx]
    norm_num
  change localRotationOperator (spherePole 7).val (southFiberPoint q).val v = _
  rw [localRotationOperator_eq_comp, ContinuousLinearMap.comp_apply]
  simp only [hyperplaneReflectionOperator_apply, hx, one_pow, hsum,
    inner_sub_right, real_inner_smul_right, inner_add_left, inner_add_right,
    hxp, real_inner_self_eq_norm_sq]
  norm_num
  module

theorem southQuarterTurn_firstAxis (q : Sphere 3) (w : ℍ) :
    southQuarterTurn q (firstAxis w) = firstAxis w - w.re • (spherePole 7).val +
      w.re • (southFiberPoint q).val := by
  rw [southQuarterTurn_formula, sourcePole_inner, first_firstAxis,
    inner_firstAxis _ (first_southFiberPoint q), add_zero, sub_zero]

theorem southQuarterTurn_radial (q : Sphere 3) :
    southQuarterTurn q (southFiberPoint q).val = -(spherePole 7).val := by
  rw [southQuarterTurn_formula, southFiber_orthogonal_sourcePole,
    real_inner_self_eq_norm_sq, mem_sphere_zero_iff_norm.mp (southFiberPoint q).property]
  norm_num
  module

theorem chartNormalAmbient_eq_quarterTurn (q : Sphere 3) (w : ℍ) :
    chartNormalAmbient q w =
      southQuarterTurn q (firstAxis (w * second (southFiberPoint q).val)) := by
  rw [chartNormalAmbient_apply, southQuarterTurn_firstAxis]

theorem southNormalFrame_rescaled (q : Sphere 3) (r : ℝ) (w : ℍ) :
    southNormalFrame.ambient q (WithLp.toLp 2 ((2 : ℝ) * r, (2 : ℝ) • w)) =
      firstAxis (w * second (southFiberPoint q).val) + r • (southFiberPoint q).val := by
  apply first_second_ext
  · rw [southNormalFrame_first, map_add, first_firstAxis, map_smul, first_southFiberPoint,
      smul_zero, add_zero, second_southFiberPoint]
    change (1 / 2 : ℝ) • (((2 : ℝ) • w) *
      Quaternion.linearIsometryEquivTuple.symm q.val) = _
    rw [smul_mul_assoc, smul_smul]
    norm_num
  · rw [southNormalFrame_second, map_add, second_firstAxis, map_smul, zero_add,
      second_southFiberPoint]
    change (1 / 2 : ℝ) • ((2 * r) • Quaternion.linearIsometryEquivTuple.symm q.val) = _
    rw [smul_smul]
    congr 1
    ring

theorem southQuarterTurn_normalFrame (q : Sphere 3) (r : ℝ) (w : ℍ) :
    southQuarterTurn q
      (southNormalFrame.ambient q (WithLp.toLp 2 ((2 : ℝ) * r, (2 : ℝ) • w))) =
      chartNormalAmbient q w - r • (spherePole 7).val := by
  rw [southNormalFrame_rescaled, map_add, map_smul, ← chartNormalAmbient_eq_quarterTurn,
    southQuarterTurn_radial, smul_neg, ← sub_eq_add_neg]

theorem stabilized_southChartFrame_comparison (q : Sphere 3) (v : V 4) (u : ℝ) :
    letI := regularFiberAtlas sphereMap contMDiff_sphereMap south south_regular 3
      (by simp only [finrank_euclideanSpace_fin]);
    StereographicEquator.lift 7 (southChartFrame.ambient (southFiberDiffeomorph q) v) +
        u • (spherePole 7).val =
      southQuarterTurn q (southNormalFrame.ambient q
        (WithLp.toLp 2 ((2 : ℝ) * (-u), (2 : ℝ) • targetTailChartEquiv.symm v))) := by
  let := regularFiberAtlas sphereMap contMDiff_sphereMap south south_regular 3
    (by simp only [finrank_euclideanSpace_fin])
  rw [lift_southChartFrame_parametrized, southQuarterTurn_normalFrame, neg_smul, sub_neg_eq_add]

end NoExoticSixSphere.QuaternionicHopf
