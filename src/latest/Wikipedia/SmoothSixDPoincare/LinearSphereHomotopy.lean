import Wikipedia.SmoothSixDPoincare.PuncturedRadialHomotopy
import Wikipedia.HopfProblem.DegreeCollapseInvertibleFrameJoin

/-!
# Actual normalized linear sphere maps along determinant-component paths

Normalize the original operator applied to the original unit vector.
A path in the proved determinant component is pointwise injective, hence
gives a genuine sphere-valued homotopy without passing through zero.
-/

noncomputable section

open Set Metric ContinuousMap Function Module
open scoped unitInterval

namespace Wikipedia.SmoothSixDPoincare.LinearSphereAction

open Wikipedia.HopfProblem.DegreeCollapse.LinearFramePaths

section Maps

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def puncturedMap (A : E →L[ℝ] F) (hi : Injective A) :
    C(sphere (0 : E) 1, PuncturedRadial.Space F) :=
  ⟨fun x => ⟨A x.val, fun h =>
    ne_zero_of_mem_unit_sphere x (hi (h.trans (map_zero A).symm))⟩,
    (A.continuous.comp continuous_subtype_val).subtype_mk _⟩

def sphereMap (A : E →L[ℝ] F) (hi : Injective A) :
    C(sphere (0 : E) 1, sphere (0 : F) 1) :=
  PuncturedRadial.toSphere.comp (puncturedMap A hi)

theorem sphereMap_coe (A : E →L[ℝ] F) (hi : Injective A)
    (x : sphere (0 : E) 1) :
    (sphereMap A hi x).val = ‖A x.val‖⁻¹ • A x.val := rfl

theorem sphereMap_id : sphereMap (ContinuousLinearMap.id ℝ E) injective_id =
    ContinuousMap.id (sphere (0 : E) 1) := by
  ext x
  change ‖(x : E)‖⁻¹ • (x : E) = (x : E)
  rw [mem_sphere_zero_iff_norm.mp x.property, inv_one, one_smul]

end Maps

section Components

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {signWeight : ℝ}

theorem component_injective (A : operatorComponent (D := E) signWeight) : Injective A.val := by
  have hd : A.val.toLinearMap.det ≠ 0 := by
    intro hz
    have hp : 0 < signWeight * A.val.toLinearMap.det := A.property
    rw [hz, mul_zero] at hp
    exact lt_irrefl _ hp
  apply LinearMap.ker_eq_bot.mp
  by_contra hk
  exact hd (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hk)

def componentHomotopy {A B : operatorComponent (D := E) signWeight} (γ : Path A B) :
    (sphereMap A.val (component_injective A)).Homotopy
      (sphereMap B.val (component_injective B)) where
  toFun q := sphereMap (γ q.1).val (component_injective (γ q.1)) q.2
  continuous_toFun := by
    have hA : Continuous (fun q : I × sphere (0 : E) 1 => (γ q.1).val) :=
      continuous_subtype_val.comp (γ.continuous.comp continuous_fst)
    have hx : Continuous (fun q : I × sphere (0 : E) 1 => q.2.val) :=
      continuous_subtype_val.comp continuous_snd
    exact PuncturedRadial.toSphere.continuous.comp ((hA.clm_apply hx).subtype_mk _)
  map_zero_left x := by
    change sphereMap (γ 0).val (component_injective (γ 0)) x = _
    rw [γ.source]
  map_one_left x := by
    change sphereMap (γ 1).val (component_injective (γ 1)) x = _
    rw [γ.target]

variable {ι : Type*} [Finite ι] [Nontrivial ι]

/-- The actual determinant-component path gives a homotopy of the actual normalized maps. -/
theorem homotopic_of_det_mul_pos (b : Basis ι ℝ E) (A B : E ≃L[ℝ] E)
    (h : 0 < A.toLinearEquiv.toLinearMap.det * B.toLinearEquiv.toLinearMap.det) :
    (sphereMap A.toContinuousLinearMap A.injective).Homotopic
      (sphereMap B.toContinuousLinearMap B.injective) := by
  have hd : A.toLinearEquiv.toLinearMap.det ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at h
    exact lt_irrefl _ h
  let A' : operatorComponent (D := E) A.toLinearEquiv.toLinearMap.det :=
    ⟨A.toContinuousLinearMap, mul_self_pos.mpr hd⟩
  let B' : operatorComponent (D := E) A.toLinearEquiv.toLinearMap.det :=
    ⟨B.toContinuousLinearMap, h⟩
  exact ⟨componentHomotopy (joined_operatorComponent b A' B').somePath⟩

end Components

end Wikipedia.SmoothSixDPoincare.LinearSphereAction
