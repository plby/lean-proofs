import Wikipedia.NoExoticSixSphere.DoubleCrossingSpherePairDerivative
import Wikipedia.NoExoticSixSphere.DoubleCrossingSpherePairIntersections

/-!
# Both actual reference-pair intersections are transverse

At the first crossing the tangent images are the coordinate axes. At the
second, splitting off the fixed axis in each target factor gives explicit
preimages for every target vector. The complete coincidence calculation
then proves transversality at every mutual intersection.
-/

noncomputable section

open Function

namespace NoExoticSixSphere.DoubleCrossingSpherePair

open GLOrthonormalization SphereCylinder SphereThreeTangentFrame
open WhitneySphere (head head_apply)

theorem exists_native_tangent_preimage (x : Sphere 3) (v : Vector 4)
    (hv : inner ℝ x.val v = 0) : ∃ u, inclusionDerivative x u = v := by
  have h : v ∈ (inclusionDerivative x).range := by
    rw [range_inclusionDerivative]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hv
  exact h

theorem transverse_first :
    Surjective ((leftDerivative (endPole 2 false)).coprod
      (rightDerivative (endPole 2 false))) := by
  intro w
  obtain ⟨u, hu⟩ := exists_native_tangent_preimage (endPole 2 false) (join 2 (0, w.1))
    (WhitneySphere.inner_endPole_join false w.1)
  obtain ⟨v, hv⟩ := exists_native_tangent_preimage (endPole 2 false) (join 2 (0, w.2))
    (WhitneySphere.inner_endPole_join false w.2)
  refine ⟨(u, v), ?_⟩
  change leftDerivative (endPole 2 false) u + rightDerivative (endPole 2 false) v = w
  rw [leftDerivative_apply, rightDerivative_apply, hu, hv, leftLinear_apply, rightLinear_apply]
  simp only [head_apply, join_head, tail_join, zero_smul, Prod.mk_add_mk, add_zero, zero_add]

theorem inner_join (t s : ℝ) (u v : Vector 3) :
    inner ℝ (join 2 (t, u)) (join 2 (s, v)) = t * s + inner ℝ u v := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ, mul_comm]

theorem second_tangent (s : ℝ) (u : Vector 3) :
    inner ℝ secondSource.val (join 2 (s, u - inner ℝ axis u • axis)) = 0 := by
  change inner ℝ (join 2 (0, axis)) (join 2 (s, u - inner ℝ axis u • axis)) = 0
  rw [inner_join]
  simp only [zero_mul, zero_add, inner_sub_right, inner_smul_right,
    real_inner_self_eq_norm_sq, norm_axis, one_pow, mul_one, sub_self]

theorem transverse_second :
    Surjective ((leftDerivative secondSource).coprod (rightDerivative secondSource)) := by
  intro w
  obtain ⟨u, hu⟩ := exists_native_tangent_preimage secondSource
    (join 2 (inner ℝ axis w.2, w.1 - inner ℝ axis w.1 • axis))
      (second_tangent (inner ℝ axis w.2) w.1)
  obtain ⟨v, hv⟩ := exists_native_tangent_preimage secondSource
    (join 2 (inner ℝ axis w.1, w.2 - inner ℝ axis w.2 • axis))
      (second_tangent (inner ℝ axis w.1) w.2)
  refine ⟨(u, v), ?_⟩
  change leftDerivative secondSource u + rightDerivative secondSource v = w
  rw [leftDerivative_apply, rightDerivative_apply, hu, hv, leftLinear_apply, rightLinear_apply]
  simp only [head_apply, join_head, tail_join, Prod.mk_add_mk]
  apply Prod.ext <;> module

theorem pairTransverse (x y : Sphere 3) (h : left x = right y) :
    Surjective ((leftDerivative x).coprod (rightDerivative y)) := by
  rcases (coincidence_iff x y).mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact transverse_first
  · exact transverse_second

end NoExoticSixSphere.DoubleCrossingSpherePair
