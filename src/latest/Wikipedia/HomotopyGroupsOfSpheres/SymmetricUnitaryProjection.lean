import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryCongruence
import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryStabilization
import Mathlib.Topology.Homotopy.Basic

/-! # The actual unitary-to-symmetric projection and based homotopies -/

noncomputable section

open scoped Matrix unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices

variable {N : Type*} [Fintype N] [DecidableEq N]

def unitaryProjection : C(unitary (Matrix N N ℂ), Space N) where
  toFun U := congruence U identity
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    change Continuous (fun U : unitary (Matrix N N ℂ) ↦ U.val * 1 * U.val.transpose)
    have hU : Continuous (fun U : unitary (Matrix N N ℂ) ↦ U.val) := continuous_subtype_val
    exact (hU.mul continuous_const).mul hU.matrix_transpose

theorem unitaryProjection_val (U : unitary (Matrix N N ℂ)) :
    (unitaryProjection U).val.val = U.val * U.val.transpose := by
  change U.val * 1 * U.val.transpose = _
  rw [mul_one]

theorem unitaryProjection_one : unitaryProjection (1 : unitary (Matrix N N ℂ)) = identity :=
  congruence_one identity

theorem unitaryProjection_eq_identity_of_real (U : unitary (Matrix N N ℂ))
    (hU : ∀ i j, star (U.val i j) = U.val i j) : unitaryProjection U = identity := by
  apply Subtype.ext
  apply Subtype.ext
  rw [unitaryProjection_val]
  have ht : U.val.transpose = star U.val := by
    apply Matrix.ext
    intro i j
    exact (hU j i).symm
  rw [ht]
  exact U.property.2

theorem unitaryProjection_border {n : ℕ} (U : unitary (Matrix (Fin n) (Fin n) ℂ)) :
    unitaryProjection (MatrixBorder.unitaryBorder (1, U)) =
      stabilization n (unitaryProjection U) := by
  apply Subtype.ext
  apply Subtype.ext
  rw [unitaryProjection_val, stabilization_val, unitaryProjection_val]
  change MatrixBorder.border 1 U.val * (MatrixBorder.border 1 U.val).transpose = _
  rw [MatrixBorder.transpose_border, ← MatrixBorder.border_mul, one_mul]

def unitaryProjectionHomotopyRel {X : Type*} [TopologicalSpace X]
    {f g : C(X, unitary (Matrix N N ℂ))} (H : f.Homotopy g) (x : X)
    (hH : ∀ t i j, star ((H (t, x)).val i j) = (H (t, x)).val i j) :
    (unitaryProjection.comp f).HomotopyRel (unitaryProjection.comp g) {x} where
  toHomotopy := (ContinuousMap.Homotopy.refl unitaryProjection).comp H
  prop' t y hy := by
    have he : y = x := Set.mem_singleton_iff.mp hy
    subst y
    change unitaryProjection (H (t, x)) = unitaryProjection (f x)
    rw [unitaryProjection_eq_identity_of_real _ (hH t)]
    have h₀ := unitaryProjection_eq_identity_of_real (H (0, x)) (hH 0)
    rw [H.apply_zero] at h₀
    exact h₀.symm

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices
