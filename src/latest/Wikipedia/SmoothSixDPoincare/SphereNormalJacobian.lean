import Wikipedia.SmoothSixDPoincare.SphereBoundaryKernel
import Wikipedia.SmoothSixDPoincare.RegularValues

/-!
# Signed normal Jacobians on an actual unit sphere

An invertible normal derivative identifies its target with the tangent space
of the sphere. Composing its inverse with the actual inclusion differential,
and adding the outward radial vector, gives a frame in the ambient vector
space. A single fixed ambient identification then gives a nonzero determinant.
This convention does not choose a separate orientation at each intersection.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.SphereNormalCoordinates

variable {V N : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup N] [NormedSpace ℝ N]
  {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)]

/-- The actual inclusion differential, with its native tangent model made explicit. -/
def inclusionDerivative (x : Metric.sphere (0 : V) 1) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] V :=
  mvfderiv (𝓡 n) (Subtype.val : Metric.sphere (0 : V) 1 → V) x

theorem inner_inclusionDerivative_zero (x : Metric.sphere (0 : V) 1)
    (u : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (x : V) (inclusionDerivative x u) = 0 := by
  apply Submodule.mem_orthogonal_singleton_iff_inner_right.mp
  rw [← range_mvfderiv_subtypeVal (n := n) x]
  exact ⟨u, rfl⟩

theorem inner_self_eq_one (x : Metric.sphere (0 : V) 1) : inner ℝ (x : V) x = 1 := by
  have hx : ‖(x : V)‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using x.property
  rw [real_inner_self_eq_norm_sq, hx, one_pow]

/-- The outward radial direction followed by the inverse normal derivative. -/
def normalFrame (x : Metric.sphere (0 : V) 1)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] N) : (ℝ × N) →L[ℝ] V :=
  ((ContinuousLinearMap.id ℝ ℝ).smulRight (x : V)).coprod
    ((inclusionDerivative x).comp A.inverse)

theorem normalFrame_apply (x : Metric.sphere (0 : V) 1)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] N) (z : ℝ × N) :
    normalFrame x A z = z.1 • (x : V) + inclusionDerivative x (A.inverse z.2) := rfl

theorem inner_normalFrame (x : Metric.sphere (0 : V) 1)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] N) (z : ℝ × N) :
    inner ℝ (x : V) (normalFrame x A z) = z.1 := by
  rw [normalFrame_apply, inner_add_right, inner_smul_right,
    inner_self_eq_one, inner_inclusionDerivative_zero, mul_one, add_zero]

/-- The radial normal frame is an actual linear isomorphism whenever the normal derivative is. -/
theorem bijective_normalFrame (x : Metric.sphere (0 : V) 1)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] N) (hA : A.IsInvertible) :
    Bijective (normalFrame x A) := by
  constructor
  · intro z w hzw
    have hfst : z.1 = w.1 := by
      simpa only [inner_normalFrame] using congrArg (fun v : V => inner ℝ (x : V) v) hzw
    have ht : inclusionDerivative x (A.inverse z.2) =
        inclusionDerivative x (A.inverse w.2) := by
      rw [normalFrame_apply, normalFrame_apply, hfst] at hzw
      exact add_left_cancel hzw
    have hJ : Injective (inclusionDerivative (n := n) x) :=
      injective_mvfderiv_subtypeVal_sphere x
    exact Prod.ext hfst (hA.inverse.injective (hJ ht))
  · intro v
    have ht : v - inner ℝ (x : V) v • (x : V) ∈
        (inclusionDerivative (n := n) x).range := by
      change v - inner ℝ (x : V) v • (x : V) ∈
        (mvfderiv (𝓡 n) (Subtype.val : Metric.sphere (0 : V) 1 → V) x).range
      rw [range_mvfderiv_subtypeVal]
      apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
      rw [inner_sub_right, inner_smul_right, inner_self_eq_one, mul_one, sub_self]
    obtain ⟨u, hu⟩ := ht
    change inclusionDerivative x u = v - inner ℝ (x : V) v • (x : V) at hu
    refine ⟨(inner ℝ (x : V) v, A u), ?_⟩
    rw [normalFrame_apply, hA.inverse_apply_self, hu]
    abel

variable [FiniteDimensional ℝ V]

/-- A signed normal Jacobian, using one fixed identification for all points. -/
def normalJacobian (j : (ℝ × N) ≃L[ℝ] V) (x : Metric.sphere (0 : V) 1)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] N) : ℝ :=
  ((normalFrame x A).comp j.symm.toContinuousLinearMap).det

theorem normalJacobian_ne_zero (j : (ℝ × N) ≃L[ℝ] V) (x : Metric.sphere (0 : V) 1)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] N) (hA : A.IsInvertible) :
    normalJacobian j x A ≠ 0 := by
  apply (RegularValues.bijective_iff_det_ne_zero _).mp
  exact (bijective_normalFrame x A hA).comp j.symm.bijective

omit [FiniteDimensional ℝ V] in
/-- Changing the fixed ambient identification multiplies all Jacobians by one fixed factor. -/
theorem normalJacobian_change_reference (j k : (ℝ × N) ≃L[ℝ] V)
    (x : Metric.sphere (0 : V) 1) (A : EuclideanSpace ℝ (Fin n) →L[ℝ] N) :
    normalJacobian k x A = normalJacobian j x A *
      (j.toContinuousLinearMap.comp k.symm.toContinuousLinearMap).det := by
  have heq : (normalFrame x A).comp k.symm.toContinuousLinearMap =
      ((normalFrame x A).comp j.symm.toContinuousLinearMap).comp
        (j.toContinuousLinearMap.comp k.symm.toContinuousLinearMap) := by
    ext v
    simp
  unfold normalJacobian
  rw [heq]
  exact LinearMap.det_comp _ _

/-- Whether two intersection signs are opposite does not depend on the fixed reference frame. -/
theorem opposite_normalJacobians_change_reference (j k : (ℝ × N) ≃L[ℝ] V)
    (x y : Metric.sphere (0 : V) 1)
    (A B : EuclideanSpace ℝ (Fin n) →L[ℝ] N) :
    normalJacobian k x A * normalJacobian k y B < 0 ↔
      normalJacobian j x A * normalJacobian j y B < 0 := by
  let c := (j.toContinuousLinearMap.comp k.symm.toContinuousLinearMap).det
  have hc : c ≠ 0 :=
    (RegularValues.bijective_iff_det_ne_zero _).mp (j.bijective.comp k.symm.bijective)
  have hsq : 0 < c ^ 2 := sq_pos_of_ne_zero hc
  rw [normalJacobian_change_reference j k x A, normalJacobian_change_reference j k y B]
  change (normalJacobian j x A * c) * (normalJacobian j y B * c) < 0 ↔ _
  have heq : (normalJacobian j x A * c) * (normalJacobian j y B * c) =
      (normalJacobian j x A * normalJacobian j y B) * c ^ 2 := by ring
  rw [heq]
  constructor
  · intro h
    rcases mul_neg_iff.mp h with ⟨_, hn⟩ | ⟨ha, _⟩
    · exact (not_lt_of_gt hsq hn).elim
    · exact ha
  · exact fun h => mul_neg_of_neg_of_pos h hsq

variable {N' : Type*} [NormedAddCommGroup N'] [NormedSpace ℝ N']

omit [FiniteDimensional ℝ V] in
/-- Changing the normal model preserves the Jacobian when its reference is transported too. -/
theorem normalJacobian_change_normal_model (r : (ℝ × N) ≃L[ℝ] V) (j : N' ≃L[ℝ] N)
    (x : Metric.sphere (0 : V) 1) (A : EuclideanSpace ℝ (Fin n) →L[ℝ] N)
    (hA : A.IsInvertible) :
    normalJacobian ((ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ) j).trans r)
      x (j.symm.toContinuousLinearMap.comp A) = normalJacobian r x A := by
  let B : EuclideanSpace ℝ (Fin n) →L[ℝ] N' := j.symm.toContinuousLinearMap.comp A
  have hj : j.symm.toContinuousLinearMap.IsInvertible := ⟨j.symm, rfl⟩
  have hB : B.IsInvertible := hj.comp hA
  have hinv (z : N) : B.inverse (j.symm z) = A.inverse z := by
    apply hB.injective
    rw [hB.self_apply_inverse]
    change j.symm z = j.symm (A (A.inverse z))
    rw [hA.self_apply_inverse]
  unfold normalJacobian
  apply congrArg ContinuousLinearMap.det
  apply ContinuousLinearMap.ext
  intro v
  change (r.symm v).1 • (x : V) + inclusionDerivative x (B.inverse (j.symm (r.symm v).2)) =
    (r.symm v).1 • (x : V) + inclusionDerivative x (A.inverse (r.symm v).2)
  rw [hinv]

end Wikipedia.SmoothSixDPoincare.SphereNormalCoordinates
