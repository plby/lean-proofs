import Wikipedia.HomotopyGroupsOfSpheres.BalancedFrameFiber

/-! # Coordinate changes between frames over the same balanced involution -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions.FrameProjection

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization

variable {n : ℕ}

theorem coordinate_self (A : Stiefel.Space (n + n) n) (h : toBalanced A = toBalanced A) :
    coordinate A A h = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  exact Stiefel.RangeCoordinates.adjoint_self A x

theorem coordinate_mul (A B C : Stiefel.Space (n + n) n)
    (hAB : toBalanced A = toBalanced B) (hBC : toBalanced B = toBalanced C)
    (hAC : toBalanced A = toBalanced C) :
    coordinate A B hAB * coordinate B C hBC = coordinate A C hAC := by
  apply Subtype.ext
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  change A.val.adjoint (B.val (B.val.adjoint (C.val x))) = A.val.adjoint (C.val x)
  apply congrArg A.val.adjoint
  apply Stiefel.RangeCoordinates.self_adjoint
  rw [(toBalanced_eq_iff_range B C).mp hBC]
  exact ⟨x, rfl⟩

theorem continuous_coordinate_family {X : Type*} [TopologicalSpace X]
    (A B : X → Stiefel.Space (n + n) n) (hA : Continuous A) (hB : Continuous B)
    (h : ∀ x, toBalanced (A x) = toBalanced (B x)) :
    Continuous (fun x ↦ coordinate (A x) (B x) (h x)) := by
  have hc : Continuous (fun x ↦ (A x).val.adjoint.comp (B x).val) :=
    (ContinuousLinearMap.adjoint.continuous.comp (continuous_subtype_val.comp hA)).clm_comp
      (continuous_subtype_val.comp hB)
  exact (hc.subtype_mk _).subtype_mk _

end Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions.FrameProjection
