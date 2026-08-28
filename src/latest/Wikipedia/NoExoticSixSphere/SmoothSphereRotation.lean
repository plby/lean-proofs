import Wikipedia.NoExoticSixSphere.OrthogonalRotations
import Wikipedia.NoExoticSixSphere.EquatorDimension
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Smooth local rotations of the actual sphere

The existing product of hyperplane reflections is smooth as an action when
the reflection normals stay nonzero. Each individual rotation restricts to
a diffeomorphism of the sphere's original smooth atlas. Near the diagonal,
these diffeomorphisms move the specified point exactly and specialize to
the identity on the diagonal.
-/

open scoped Manifold ContDiff

namespace NoExoticSixSphere

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [TopologicalSpace M] [ChartedSpace H M]

omit [FiniteDimensional ℝ E] in
theorem contDiffAt_hyperplaneReflectionOperator (v : E) (hn : v ≠ 0) :
    ContDiffAt ℝ ∞ hyperplaneReflectionOperator v := by
  have heq : hyperplaneReflectionOperator (E := E) = fun w ↦
      (1 : E →L[ℝ] E) - (2 * (‖w‖ ^ 2)⁻¹) • (innerSL ℝ w).smulRight w := by
    funext w
    apply ContinuousLinearMap.ext
    intro z
    simp only [hyperplaneReflectionOperator_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.one_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_smul]
  rw [heq]
  have hnorm : ContDiffAt ℝ ∞ (fun w : E ↦ ‖w‖ ^ 2) v :=
    (contDiff_id.norm_sq (𝕜 := ℝ)).contDiffAt
  exact contDiffAt_const.sub
    ((contDiffAt_const.mul (hnorm.inv (pow_ne_zero 2 (norm_ne_zero_iff.mpr hn)))).smul
      ((innerSL ℝ).contDiff.contDiffAt.smulRight contDiffAt_id))

omit [FiniteDimensional ℝ E] in
theorem contMDiff_hyperplaneReflectionOperator {v : M → E}
    (hv : ContMDiff I 𝓘(ℝ, E) ∞ v) (hn : ∀ x, v x ≠ 0) :
    ContMDiff I 𝓘(ℝ, E →L[ℝ] E) ∞ (fun x ↦ hyperplaneReflectionOperator (v x)) := by
  intro x
  exact (contDiffAt_hyperplaneReflectionOperator (v x) (hn x)).comp_contMDiffAt (hv x)

omit [FiniteDimensional ℝ E] in
theorem contMDiff_localRotationOperator {v w : M → E}
    (hv : ContMDiff I 𝓘(ℝ, E) ∞ v) (hw : ContMDiff I 𝓘(ℝ, E) ∞ w)
    (hwn : ∀ x, w x ≠ 0) (hvn : ∀ x, v x + w x ≠ 0) :
    ContMDiff I 𝓘(ℝ, E →L[ℝ] E) ∞ (fun x ↦ localRotationOperator (v x) (w x)) := by
  have h := (contMDiff_hyperplaneReflectionOperator hw hwn).clm_comp
    (contMDiff_hyperplaneReflectionOperator (hv.add hw) hvn)
  simpa only [localRotationOperator_eq_comp, Pi.add_apply] using h

omit [FiniteDimensional ℝ E] in
theorem contMDiff_hyperplaneReflection_apply {v z : M → E}
    (hv : ContMDiff I 𝓘(ℝ, E) ∞ v) (hz : ContMDiff I 𝓘(ℝ, E) ∞ z)
    (hn : ∀ x, v x ≠ 0) :
    ContMDiff I 𝓘(ℝ, E) ∞ (fun x ↦ hyperplaneReflectionOperator (v x) (z x)) := by
  have hnorm : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x ↦ ‖v x‖ ^ 2) :=
    (contDiff_id.norm_sq (𝕜 := ℝ) : ContDiff ℝ ∞ (fun y : E ↦ ‖y‖ ^ 2)).contMDiff.comp hv
  have hinv : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x ↦ (‖v x‖ ^ 2)⁻¹) := by
    intro x
    have hrec : ContDiffAt ℝ ∞ (fun r : ℝ ↦ r⁻¹) (‖v x‖ ^ 2) :=
      contDiffAt_id.inv (pow_ne_zero 2 (norm_ne_zero_iff.mpr (hn x)))
    exact hrec.comp_contMDiffAt (f := fun y ↦ ‖v y‖ ^ 2) (x := x) (hnorm x)
  have hinner : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x ↦ inner ℝ (v x) (z x)) :=
    (contDiff_inner : ContDiff ℝ ∞ (fun p : E × E ↦ inner ℝ p.1 p.2)).contMDiff.comp
      (hv.prodMk_space hz)
  have heq : (fun x ↦ hyperplaneReflectionOperator (v x) (z x)) =
      fun x ↦ z x - (2 * (‖v x‖ ^ 2)⁻¹ * inner ℝ (v x) (z x)) • v x :=
    funext (fun x ↦ hyperplaneReflectionOperator_apply (v x) (z x))
  rw [heq]
  exact hz.sub (((contMDiff_const.mul hinv).mul hinner).smul hv)

omit [FiniteDimensional ℝ E] in
theorem contMDiff_localRotation_apply {v w z : M → E}
    (hv : ContMDiff I 𝓘(ℝ, E) ∞ v) (hw : ContMDiff I 𝓘(ℝ, E) ∞ w)
    (hz : ContMDiff I 𝓘(ℝ, E) ∞ z) (hwn : ∀ x, w x ≠ 0)
    (hvn : ∀ x, v x + w x ≠ 0) :
    ContMDiff I 𝓘(ℝ, E) ∞ (fun x ↦ localRotationOperator (v x) (w x) (z x)) := by
  have h := contMDiff_hyperplaneReflection_apply hw
    (contMDiff_hyperplaneReflection_apply (hv.add hw) hz hvn) hwn
  exact h

variable {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]

noncomputable def unitSphereDiffeomorph (e : E ≃ₗᵢ[ℝ] E) :
    UnitSphere E ≃ₘ⟮𝓡 n, 𝓡 n⟯ UnitSphere E where
  toEquiv := (unitSphereCongr e).toEquiv
  contMDiff_toFun :=
    (e.toContinuousLinearEquiv.contDiff.contMDiff.comp contMDiff_coe_sphere).codRestrict_sphere _
  contMDiff_invFun :=
    (e.symm.toContinuousLinearEquiv.contDiff.contMDiff.comp
      contMDiff_coe_sphere).codRestrict_sphere _

noncomputable def sphereRotation (a b : UnitSphere E) :
    UnitSphere E ≃ₘ⟮𝓡 n, 𝓡 n⟯ UnitSphere E :=
  unitSphereDiffeomorph (localRotationEquiv (a : E) (b : E))

omit [FiniteDimensional ℝ E] in
theorem sphereRotation_apply (a b : UnitSphere E) : sphereRotation (n := n) a b a = b := by
  apply Subtype.ext
  exact localRotationEquiv_apply a b

omit [FiniteDimensional ℝ E] in
theorem sphereRotation_self (a z : UnitSphere E) : sphereRotation (n := n) a a z = z := by
  apply Subtype.ext
  exact congrArg (fun L : E →L[ℝ] E ↦ L (z : E)) (localRotationOperator_self (a : E))

omit [FiniteDimensional ℝ E] in
theorem contMDiff_sphereRotation_apply [IsManifold I ∞ M] {a b z : M → UnitSphere E}
    (ha : ContMDiff I (𝓡 n) ∞ a) (hb : ContMDiff I (𝓡 n) ∞ b)
    (hz : ContMDiff I (𝓡 n) ∞ z)
    (hn : ∀ x, (a x : E) + (b x : E) ≠ 0) :
    ContMDiff I (𝓡 n) ∞ (fun x ↦ sphereRotation (n := n) (a x) (b x) (z x)) := by
  have h := contMDiff_localRotation_apply (contMDiff_coe_sphere.comp ha)
    (contMDiff_coe_sphere.comp hb) (contMDiff_coe_sphere.comp hz)
    (fun x ↦ norm_ne_zero_iff.mp (by
      change ‖(b x : E)‖ ≠ 0
      rw [ClosedHemisphere.unit_norm]
      exact one_ne_zero)) hn
  exact h.codRestrict_sphere _

theorem continuous_sphereRotation_apply {X : Type*} [TopologicalSpace X]
    {a b z : X → UnitSphere E} (ha : Continuous a) (hb : Continuous b) (hz : Continuous z)
    (hn : ∀ x, (a x : E) + (b x : E) ≠ 0) :
    Continuous (fun x ↦ sphereRotation (n := n) (a x) (b x) (z x)) := by
  have h := continuous_localRotationOperator
    (fun x ↦ (a x : E)) (fun x ↦ (b x : E))
    (continuous_subtype_val.comp ha) (continuous_subtype_val.comp hb)
    (fun x ↦ norm_ne_zero_iff.mp (by rw [ClosedHemisphere.unit_norm]; exact one_ne_zero)) hn
  exact (h.clm_apply (continuous_subtype_val.comp hz)).subtype_mk _

end NoExoticSixSphere
