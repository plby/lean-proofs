import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Stereographic coordinates with identity tangent derivative

The pole is the antipode of the chosen point. The inverse chart sends zero
to that point, and its ambient derivative at zero is the tangent inclusion.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HomotopyGroupsOfSpheres.SphereCenteredCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

abbrev UnitSphere (E : Type*) [NormedAddCommGroup E] := Metric.sphere (0 : E) 1

abbrev Tangent (z : UnitSphere E) := (ℝ ∙ (-z.val))ᗮ

def chart (z : UnitSphere E) : OpenPartialHomeomorph (UnitSphere E) (Tangent z) :=
  stereographic (by simp)

def inverse (z : UnitSphere E) : Tangent z → UnitSphere E :=
  stereoInvFun (by simp)

theorem inverse_eq_chart_symm (z : UnitSphere E) : inverse z = (chart z).symm := rfl

@[simp] theorem chart_target (z : UnitSphere E) : (chart z).target = Set.univ := rfl

@[simp] theorem inverse_zero (z : UnitSphere E) : inverse z 0 = z := by
  apply Subtype.ext
  simp [inverse, stereoInvFun, stereoInvFunAux, smul_smul]

theorem contDiff_inverse_val (z : UnitSphere E) {n : ℕ∞ω} :
    ContDiff ℝ n (fun w : Tangent z ↦ (inverse z w).val) :=
  contDiff_stereoInvFunAux.comp (Tangent z).subtypeL.contDiff

theorem hasFDerivAt_inverse_val (z : UnitSphere E) :
    HasFDerivAt (fun w : Tangent z ↦ (inverse z w).val) (Tangent z).subtypeL 0 :=
  hasFDerivAt_stereoInvFunAux_comp_coe (-z.val)

theorem hasDerivAt_inverse_line (z : UnitSphere E) (v : Tangent z) :
    HasDerivAt (fun t : ℝ ↦ (inverse z (t • v)).val) v.val 0 := by
  have hf : HasFDerivAt (fun w : Tangent z ↦ (inverse z w).val)
      (Tangent z).subtypeL ((0 : ℝ) • v) := by
    simpa only [zero_smul] using hasFDerivAt_inverse_val z
  have h := hf.comp_hasDerivAt 0
    ((hasDerivAt_id (0 : ℝ)).smul_const v)
  convert h using 1 <;> try rfl
  simp only [one_smul, Submodule.subtypeL_apply]

theorem inverse_injective (z : UnitSphere E) : Function.Injective (inverse z) := by
  intro v w h
  have he := congrArg (chart z) h
  simpa only [inverse_eq_chart_symm, (chart z).right_inv (Set.mem_univ v),
    (chart z).right_inv (Set.mem_univ w)] using he

theorem self_mem_chart_source (z : UnitSphere E) : z ∈ (chart z).source := by
  have h := (chart z).map_target (show (0 : Tangent z) ∈ (chart z).target from Set.mem_univ 0)
  change inverse z 0 ∈ (chart z).source at h
  simpa only [inverse_zero] using h

@[simp] theorem chart_self (z : UnitSphere E) : chart z z = 0 := by
  have h := (chart z).right_inv (show (0 : Tangent z) ∈ (chart z).target from Set.mem_univ 0)
  change chart z (inverse z 0) = 0 at h
  simpa only [inverse_zero] using h

theorem contDiffAt_stereoToFun (z : UnitSphere E) {n : ℕ∞ω} :
    ContDiffAt ℝ n (stereoToFun (-z.val)) z.val := by
  have hne : (1 : ℝ) - innerSL ℝ (-z.val) z.val ≠ 0 := by
    simp [innerSL_apply_apply]
  exact ((contDiffAt_const.div
    (contDiffAt_const.sub (innerSL ℝ (-z.val)).contDiff.contDiffAt) hne).smul
      (Tangent z).orthogonalProjectionOnto.contDiff.contDiffAt)

theorem tangent_finrank (z : UnitSphere E) {n : ℕ}
    [Fact (Module.finrank ℝ E = n + 1)] : Module.finrank ℝ (Tangent z) = n := by
  apply Submodule.finrank_orthogonal_span_singleton
  intro h
  have hz : ‖z.val‖ = 1 := mem_sphere_zero_iff_norm.mp z.property
  have hz0 : z.val = 0 := neg_eq_zero.mp h
  rw [hz0, norm_zero] at hz
  exact zero_ne_one hz

end Wikipedia.HomotopyGroupsOfSpheres.SphereCenteredCoordinates
