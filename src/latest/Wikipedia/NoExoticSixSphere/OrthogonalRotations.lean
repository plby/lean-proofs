import Wikipedia.NoExoticSixSphere.GLDeformation
import Wikipedia.NoExoticSixSphere.SphereNormalization
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# Continuous local orthogonal rotations

A product of two hyperplane reflections moves one unit vector to another. It
depends continuously on the pair away from antipodal pairs and is the identity
when the two vectors agree. This provides the local orthogonal transport used
to change a column along a sphere homotopy.
-/

namespace NoExoticSixSphere

variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace X]

/-- Reflection in the hyperplane perpendicular to an ambient vector, as an operator. -/
noncomputable def hyperplaneReflectionOperator (v : E) : E →L[ℝ] E :=
  ((ℝ ∙ v)ᗮ.reflection).toContinuousLinearEquiv.toContinuousLinearMap

omit [FiniteDimensional ℝ E] in
/-- The reflection operator has the usual rational rank-one formula. -/
theorem hyperplaneReflectionOperator_apply (v w : E) :
    hyperplaneReflectionOperator v w =
      w - (2 * (‖v‖ ^ 2)⁻¹ * inner ℝ v w) • v := by
  change (ℝ ∙ v)ᗮ.reflection w = _
  rw [Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply]
  simp only [RCLike.ofReal_real_eq_id, id_eq, neg_sub, two_smul]
  rw [← add_smul]
  apply congrArg (fun r : ℝ ↦ w - r • v)
  simp only [div_eq_mul_inv]
  ring

/-- Hyperplane reflection is continuous in the nonzero normal vector, in operator norm. -/
theorem continuous_hyperplaneReflectionOperator (v : X → E) (hv : Continuous v)
    (hn : ∀ x, v x ≠ 0) : Continuous (fun x ↦ hyperplaneReflectionOperator (v x)) := by
  apply continuous_clm_apply.mpr
  intro w
  have heq : (fun x ↦ hyperplaneReflectionOperator (v x) w) =
      fun x ↦ w - (2 * (‖v x‖ ^ 2)⁻¹ * inner ℝ (v x) w) • v x :=
    funext (fun x ↦ hyperplaneReflectionOperator_apply (v x) w)
  rw [heq]
  exact continuous_const.sub
    (((continuous_const.mul ((hv.norm.pow 2).inv₀
      (fun x ↦ pow_ne_zero _ (norm_ne_zero_iff.mpr (hn x))))).mul
      (hv.inner continuous_const)).smul hv)

/-- The product of the two actual hyperplane reflections. -/
noncomputable def localRotationEquiv (v w : E) : E ≃ₗᵢ[ℝ] E :=
  ((ℝ ∙ (v + w))ᗮ.reflection).trans ((ℝ ∙ w)ᗮ.reflection)

/-- The same rotation in operator-norm coordinates. -/
noncomputable def localRotationOperator (v w : E) : E →L[ℝ] E :=
  (localRotationEquiv v w).toContinuousLinearEquiv.toContinuousLinearMap

omit [FiniteDimensional ℝ E] in
/-- For unit vectors the reflection product carries the first vector to the second. -/
theorem localRotationEquiv_apply (v w : UnitSphere E) :
    localRotationEquiv (v : E) (w : E) (v : E) = (w : E) := by
  have heq : (ℝ ∙ ((v : E) + (w : E)))ᗮ.reflection (v : E) = -(w : E) := by
    simpa only [sub_neg_eq_add] using
      (Submodule.reflection_sub (v := (v : E)) (w := -(w : E))
        (by rw [norm_neg, ClosedHemisphere.unit_norm, ClosedHemisphere.unit_norm]))
  change (ℝ ∙ (w : E))ᗮ.reflection ((ℝ ∙ ((v : E) + (w : E)))ᗮ.reflection (v : E)) = _
  rw [heq, map_neg, Submodule.reflection_orthogonalComplement_singleton_eq_neg, neg_neg]

omit [FiniteDimensional ℝ E] in
/-- When both vectors agree, the two reflections cancel exactly. -/
theorem localRotationOperator_self (v : E) : localRotationOperator v v = 1 := by
  have hspan : ℝ ∙ (v + v) = ℝ ∙ v := by
    rw [← two_smul ℝ v]
    exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr (by norm_num : (2 : ℝ) ≠ 0)) v
  apply ContinuousLinearMap.ext
  intro w
  change (ℝ ∙ v)ᗮ.reflection ((ℝ ∙ (v + v))ᗮ.reflection w) = w
  simpa only [hspan] using (ℝ ∙ v)ᗮ.reflection_reflection w

omit [FiniteDimensional ℝ E] in
/-- Operator coordinates of the reflection product. -/
theorem localRotationOperator_eq_comp (v w : E) :
    localRotationOperator v w =
      (hyperplaneReflectionOperator w).comp (hyperplaneReflectionOperator (v + w)) := by
  apply ContinuousLinearMap.ext
  intro z
  rfl

/-- The rotation family is continuous wherever the two reflection normals stay nonzero. -/
theorem continuous_localRotationOperator (v w : X → E) (hv : Continuous v) (hw : Continuous w)
    (hwn : ∀ x, w x ≠ 0) (hvn : ∀ x, v x + w x ≠ 0) :
    Continuous (fun x ↦ localRotationOperator (v x) (w x)) := by
  have heq : (fun x ↦ localRotationOperator (v x) (w x)) =
      fun x ↦ (hyperplaneReflectionOperator (w x)).comp
        (hyperplaneReflectionOperator (v x + w x)) :=
    funext (fun x ↦ localRotationOperator_eq_comp (v x) (w x))
  rw [heq]
  exact (continuous_hyperplaneReflectionOperator w hw hwn).clm_comp
    (continuous_hyperplaneReflectionOperator (fun x ↦ v x + w x) (hv.add hw) hvn)

end NoExoticSixSphere
