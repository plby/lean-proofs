import Wikipedia.NoExoticSixSphere.SmoothRangeOrthonormalization

/-!
# The normalized frame as a smooth equivalence onto the original normal range

The existing orthonormalization is now packaged as a `SmoothRangeFrame`,
with its exact ambient operator. No homotopy invariance of collapse classes
under changes of frame is assumed here.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.SmoothRangeFrame

open GLOrthonormalization Stiefel

variable {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [TopologicalSpace M] [ChartedSpace H M] {N k : ℕ}
  {P : M → Vector N →L[ℝ] Vector N} (a : SmoothRangeFrame I P (Vector k))

def normalized : SmoothRangeFrame I P (Vector k) where
  equiv x :=
    (LinearEquiv.ofInjective (a.orthonormal x).val.toLinearMap
      (Stiefel.injective (a.orthonormal x))).toContinuousLinearEquiv.trans
        (ContinuousLinearEquiv.ofEq _ _ (a.orthonormal_range x))
  smooth := a.contMDiff_orthonormal

theorem normalized_ambient (x : M) : a.normalized.ambient x = (a.orthonormal x).val := rfl

theorem norm_normalized_ambient (x : M) (v : Vector k) :
    ‖a.normalized.ambient x v‖ = ‖v‖ := (a.orthonormal x).property v

theorem eq_of_ambient_eq (a' : SmoothRangeFrame I P (Vector k))
    (h : ∀ x, a.ambient x = a'.ambient x) : a = a' := by
  have he : a.equiv = a'.equiv := by
    funext x
    apply ContinuousLinearEquiv.ext
    funext v
    apply Subtype.ext
    exact congrArg (fun L : Vector k →L[ℝ] Vector N ↦ L v) (h x)
  cases a
  cases a'
  dsimp only at he
  cases he
  rfl

theorem normalized_eq_self (h : ∀ x v, ‖a.ambient x v‖ = ‖v‖) : a.normalized = a := by
  apply eq_of_ambient_eq
  intro x
  exact Orthonormalization.operator_eq_self a.ambient x (h x)

theorem normalized_normalized : a.normalized.normalized = a.normalized :=
  a.normalized.normalized_eq_self a.norm_normalized_ambient

end NoExoticSixSphere.SmoothRangeFrame
