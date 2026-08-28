import Wikipedia.HomotopyGroupsOfSpheres.BalancedFrameProjection
import Wikipedia.NoExoticSixSphere.OrthogonalCompactness

/-!
# The frame-projection fiber is the actual orthogonal group

Right composition changes an orthonormal frame without changing its range.
The adjoint of a fixed frame extracts the unique orthogonal coordinates of
every other frame over the same balanced involution.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions.FrameProjection

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization

variable {n : ℕ}

def orthogonalOfSquareFrame (A : Stiefel.Space n n) : OrthogonalOperators n :=
  ⟨⟨A.val, OrthogonalCompactness.normPreserving_isInvertible A.val A.property⟩, A.property⟩

def rightAction (A : Stiefel.Space (n + n) n) (g : OrthogonalOperators n) :
    Stiefel.Space (n + n) n :=
  ⟨A.val.comp g.val.val, fun x ↦ (A.property (g.val.val x)).trans (g.property x)⟩

theorem rightAction_one (A : Stiefel.Space (n + n) n) : rightAction A 1 = A := by
  apply Subtype.ext
  rfl

theorem rightAction_mul (A : Stiefel.Space (n + n) n) (g h : OrthogonalOperators n) :
    rightAction A (g * h) = rightAction (rightAction A g) h := by
  apply Subtype.ext
  rfl

theorem continuous_rightAction :
    Continuous (fun z : Stiefel.Space (n + n) n × OrthogonalOperators n ↦
      rightAction z.1 z.2) :=
  ((continuous_subtype_val.comp continuous_fst).clm_comp
    (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd))).subtype_mk _

theorem range_rightAction (A : Stiefel.Space (n + n) n) (g : OrthogonalOperators n) :
    (rightAction A g).val.range = A.val.range := by
  change (A.val.toLinearMap.comp g.val.val.toLinearMap).range = A.val.toLinearMap.range
  exact LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr g.val.property.surjective)

theorem toBalanced_rightAction (A : Stiefel.Space (n + n) n) (g : OrthogonalOperators n) :
    toBalanced (rightAction A g) = toBalanced A :=
  (toBalanced_eq_iff_range _ _).mpr (range_rightAction A g)

def coordinate (A B : Stiefel.Space (n + n) n) (h : toBalanced A = toBalanced B) :
    OrthogonalOperators n :=
  orthogonalOfSquareFrame (Stiefel.RangeCoordinates.extract A B
    ((toBalanced_eq_iff_range A B).mp h).symm.le)

theorem coordinate_operator (A B : Stiefel.Space (n + n) n)
    (h : toBalanced A = toBalanced B) :
    (coordinate A B h).val.val = A.val.adjoint.comp B.val := rfl

theorem rightAction_coordinate (A B : Stiefel.Space (n + n) n)
    (h : toBalanced A = toBalanced B) : rightAction A (coordinate A B h) = B := by
  apply Subtype.ext
  exact congrArg Subtype.val (Stiefel.RangeCoordinates.comp_extract A B
    ((toBalanced_eq_iff_range A B).mp h).symm.le)

theorem coordinate_rightAction (A : Stiefel.Space (n + n) n) (g : OrthogonalOperators n)
    (h : toBalanced A = toBalanced (rightAction A g)) :
    coordinate A (rightAction A g) h = g := by
  apply Subtype.ext
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  change A.val.adjoint (A.val (g.val.val x)) = g.val.val x
  exact Stiefel.RangeCoordinates.adjoint_self A _

def fiber (A : Stiefel.Space (n + n) n) :=
  {B : Stiefel.Space (n + n) n // toBalanced B = toBalanced A}

instance fiber_topologicalSpace (A : Stiefel.Space (n + n) n) : TopologicalSpace (fiber A) :=
  inferInstanceAs (TopologicalSpace {B : Stiefel.Space (n + n) n // toBalanced B = toBalanced A})

theorem continuous_coordinate (A : Stiefel.Space (n + n) n) :
    Continuous (fun B : fiber A ↦ coordinate A B.val B.property.symm) := by
  have hc : Continuous (fun B : fiber A ↦ A.val.adjoint.comp B.val.val) :=
    continuous_const.clm_comp (continuous_subtype_val.comp continuous_subtype_val)
  exact (hc.subtype_mk _).subtype_mk _

def fiberHomeomorph (A : Stiefel.Space (n + n) n) : OrthogonalOperators n ≃ₜ fiber A where
  toFun g := ⟨rightAction A g, toBalanced_rightAction A g⟩
  invFun B := coordinate A B.val B.property.symm
  left_inv g := coordinate_rightAction A g _
  right_inv B := Subtype.ext (rightAction_coordinate A B.val B.property.symm)
  continuous_toFun :=
    (continuous_rightAction.comp (continuous_const.prodMk continuous_id)).subtype_mk _
  continuous_invFun := continuous_coordinate A

theorem fiberHomeomorph_one (A : Stiefel.Space (n + n) n) :
    fiberHomeomorph A 1 = ⟨A, rfl⟩ := Subtype.ext (rightAction_one A)

end Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions.FrameProjection
