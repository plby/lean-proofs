import Wikipedia.NoExoticSixSphere.PartialFrameColumnBundle

/-!
# The equatorial transition of the antipodal column rotations

On the equator, the change between the two ambient column rotations acts
on the pole's orthogonal complement by reflection perpendicular to the
equatorial vector. This is an identity of the actual rotation operators;
no degree, homology, or parity calculation is assumed.
-/

noncomputable section

namespace NoExoticSixSphere.AntipodalColumnTransition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem rotation_transition (c x w : E) :
    (localRotationEquiv c x).symm (localRotationEquiv (-c) x w) =
      hyperplaneReflectionOperator (c + x) (hyperplaneReflectionOperator (-c + x) w) := by
  change (ℝ ∙ (c + x))ᗮ.reflection.symm
    ((ℝ ∙ x)ᗮ.reflection.symm ((ℝ ∙ x)ᗮ.reflection ((ℝ ∙ (-c + x))ᗮ.reflection w))) = _
  rw [Submodule.reflection_symm, Submodule.reflection_symm]
  rw [Submodule.reflection_reflection]
  rfl

theorem equatorial_norm_sq (c x : UnitSphere E) (hcx : inner ℝ c.val x.val = 0) :
    ‖c.val + x.val‖ ^ 2 = 2 := by
  rw [norm_add_sq_real, ClosedHemisphere.unit_norm, ClosedHemisphere.unit_norm, hcx]
  norm_num

theorem equatorial_transition (c x : UnitSphere E) (hcx : inner ℝ c.val x.val = 0)
    (w : E) (hcw : inner ℝ c.val w = 0) :
    (localRotationEquiv c.val x.val).symm (localRotationEquiv (-c.val) x.val w) =
      w - (2 * inner ℝ x.val w) • x.val := by
  have hnc : inner ℝ (antipode c).val x.val = 0 := by
    change inner ℝ (-c.val) x.val = 0
    rw [inner_neg_left, hcx, neg_zero]
  have hn := equatorial_norm_sq (antipode c) x hnc
  change ‖-c.val + x.val‖ ^ 2 = 2 at hn
  have hxx : inner ℝ x.val x.val = 1 := by
    rw [real_inner_self_eq_norm_sq, ClosedHemisphere.unit_norm, one_pow]
  have hcc : inner ℝ c.val c.val = 1 := by
    rw [real_inner_self_eq_norm_sq, ClosedHemisphere.unit_norm, one_pow]
  have hxc : inner ℝ x.val c.val = 0 := (real_inner_comm _ _).trans hcx
  rw [rotation_transition, hyperplaneReflectionOperator_apply,
    hyperplaneReflectionOperator_apply, equatorial_norm_sq c x hcx, hn]
  simp only [inner_add_left, inner_neg_left, inner_sub_right, inner_smul_right,
    inner_add_right, inner_neg_right, hcx, hxc, hcw, hxx, hcc]
  norm_num
  module

open GLOrthonormalization OrthogonalColumnBundle OrthogonalPaths

variable {n : ℕ}

theorem inverse_rotation_apply (c x : UnitSphere (Vector (n + 1))) (w : Vector (n + 1)) :
    (inverse (rotation c x)).val.val w = (localRotationEquiv c.val x.val).symm w := by
  apply (toEquiv (rotation c x)).injective
  change (rotation c x).val.val ((inverse (rotation c x)).val.val w) =
    localRotationEquiv c.val x.val ((localRotationEquiv c.val x.val).symm w)
  rw [self_apply_inverse, LinearIsometryEquiv.apply_symm_apply]

theorem operator_transition (c x : UnitSphere (Vector (n + 1)))
    (hcx : inner ℝ c.val x.val = 0) (w : Vector (n + 1))
    (hcw : inner ℝ c.val w = 0) :
    (inverse (rotation c x)).val.val ((rotation (antipode c) x).val.val w) =
      w - (2 * inner ℝ x.val w) • x.val := by
  rw [inverse_rotation_apply]
  exact equatorial_transition c x hcx w hcw

end NoExoticSixSphere.AntipodalColumnTransition
