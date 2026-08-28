import Wikipedia.NoExoticSixSphere.PartialFrameSphereObstruction

/-!
# Frame-coordinate changes preserve the actual sphere parity

Post- and precomposition by fixed linear isometries give genuine
homeomorphisms of partial-frame spaces. More generally, any homeomorphism
of the frame target preserves parity: its zero criterion is exact disk
extension, and the target invariant has only two values.
-/

noncomputable section

namespace NoExoticSixSphere.Stiefel

open GLOrthonormalization
open Wikipedia.HopfProblem.DegreeCollapse.DiskCylinder

theorem sphereThirdObstruction_homeomorph (r : ℕ)
    (h : Space (3 + (r + 2)) (r + 2) ≃ₜ Space (3 + (r + 2)) (r + 2))
    (f : C(Sphere 3, Space (3 + (r + 2)) (r + 2))) :
    sphereThirdObstruction r ((h : C(_, _)).comp f) = sphereThirdObstruction r f := by
  apply zmodTwo_eq_of_zero_iff
  rw [sphereThirdObstruction_zero_iff_extension, sphereThirdObstruction_zero_iff_extension]
  constructor
  · rintro ⟨F, hF⟩
    refine ⟨(h.symm : C(_, _)).comp F, ?_⟩
    intro s
    change h.symm (F (boundaryToDisk s)) = f s
    rw [hF]
    exact h.symm_apply_apply (f s)
  · rintro ⟨F, hF⟩
    refine ⟨(h : C(_, _)).comp F, ?_⟩
    intro s
    exact congrArg h (hF s)

namespace FrameCoordinates

variable {N k : ℕ} (U : Vector N ≃ₗᵢ[ℝ] Vector N) (V : Vector k ≃ₗᵢ[ℝ] Vector k)

def change (a : Space N k) : Space N k :=
  ofIsometry (U.toLinearIsometry.comp ((toIsometry a).comp V.toLinearIsometry))

theorem change_apply (a : Space N k) (w : Vector k) :
    (change U V a).val w = U (a.val (V w)) := rfl

theorem change_operator (a : Space N k) :
    (change U V a).val = U.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (a.val.comp V.toContinuousLinearEquiv.toContinuousLinearMap) := by
  apply ContinuousLinearMap.ext
  intro w
  rfl

theorem continuous_change : Continuous (change U V) := by
  have hc : Continuous (fun a : Space N k ↦ (change U V a).val) := by
    simp_rw [change_operator]
    exact continuous_const.clm_comp (continuous_subtype_val.clm_comp continuous_const)
  exact hc.subtype_mk _

def homeomorph : Space N k ≃ₜ Space N k where
  toFun := change U V
  invFun := change U.symm V.symm
  left_inv a := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro w
    simp only [change_apply, LinearIsometryEquiv.apply_symm_apply,
      LinearIsometryEquiv.symm_apply_apply]
  right_inv a := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro w
    simp only [change_apply, LinearIsometryEquiv.apply_symm_apply,
      LinearIsometryEquiv.symm_apply_apply]
  continuous_toFun := continuous_change U V
  continuous_invFun := continuous_change U.symm V.symm

end FrameCoordinates

end NoExoticSixSphere.Stiefel
