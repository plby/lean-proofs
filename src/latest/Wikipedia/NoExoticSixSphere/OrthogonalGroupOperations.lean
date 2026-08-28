import Wikipedia.NoExoticSixSphere.ColumnFiber

/-!
# Operator-norm group operations

Explicit inverse and cancellation identities for the actual nested-subtype
orthogonal operator space. These support local trivializations of the column
projection without replacing its topology by a chosen coordinate topology.
-/

namespace NoExoticSixSphere.OrthogonalPaths

open GLOrthonormalization

variable {n : ℕ}

theorem mul_apply (a b : OrthogonalOperators n) (w : Vector n) :
    (mul a b).1.1 w = a.1.1 (b.1.1 w) := rfl

theorem mul_identity (a : OrthogonalOperators n) : mul a (identity n) = a := by
  apply Subtype.ext
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro w
  rfl

theorem mul_assoc (a b c : OrthogonalOperators n) : mul (mul a b) c = mul a (mul b c) := by
  apply Subtype.ext
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro w
  rfl

/-- The actual inverse isometry, viewed in operator-norm coordinates. -/
noncomputable def inverse (a : OrthogonalOperators n) : OrthogonalOperators n :=
  ofEquiv (toEquiv a).symm

theorem inverse_operator (a : OrthogonalOperators n) : (inverse a).1.1 = a.1.1.inverse := by
  apply ContinuousLinearMap.ext
  intro w
  rfl

theorem inverse_apply_self (a : OrthogonalOperators n) (w : Vector n) :
    (inverse a).1.1 (a.1.1 w) = w := by
  rw [inverse_operator]
  exact a.1.2.inverse_apply_self w

theorem self_apply_inverse (a : OrthogonalOperators n) (w : Vector n) :
    a.1.1 ((inverse a).1.1 w) = w := by
  rw [inverse_operator]
  exact a.1.2.self_apply_inverse w

theorem inverse_mul (a : OrthogonalOperators n) : mul (inverse a) a = identity n := by
  apply Subtype.ext
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro w
  exact inverse_apply_self a w

theorem mul_inverse (a : OrthogonalOperators n) : mul a (inverse a) = identity n := by
  apply Subtype.ext
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro w
  exact self_apply_inverse a w

theorem inverse_identity : inverse (identity n) = identity n := by
  apply Subtype.ext
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro w
  exact inverse_apply_self (identity n) w

variable {X : Type*} [TopologicalSpace X]

/-- Inversion is continuous in the existing operator-norm topology. -/
theorem continuous_inverse (a : X → OrthogonalOperators n) (ha : Continuous a) :
    Continuous (fun x ↦ inverse (a x)) := by
  have hA : Continuous (fun x ↦ (a x).1.1) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp ha)
  have hinv : Continuous (fun x ↦ ((a x).1.1).inverse) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact ContinuousAt.comp (f := fun x ↦ (a x).1.1) (x := x)
      (((a x).1.2.contDiffAt_map_inverse (n := 0)).continuousAt) hA.continuousAt
  exact (hinv.subtype_mk _).subtype_mk _

end NoExoticSixSphere.OrthogonalPaths
