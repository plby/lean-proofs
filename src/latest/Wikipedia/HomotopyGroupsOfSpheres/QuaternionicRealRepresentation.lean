import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicLinearAction
import Wikipedia.NoExoticSixSphere.OrthogonalLieGroup
import Wikipedia.NoExoticSixSphere.OrthogonalCompactness

/-! # Faithful real orthogonal representation of the quaternionic unitary group -/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns

open QuaternionicRankOne NoExoticSixSphere.GLOrthonormalization

local notation "ℍ" => Quaternion ℝ

theorem realAction_add (n : ℕ) (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ) :
    realAction n (A + B) = realAction n A + realAction n B := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [realAction_apply, Matrix.add_mulVec, WithLp.toLp_add,
    map_add, add_apply]

theorem realAction_smul (n : ℕ) (c : ℝ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ) :
    realAction n (c • A) = c • realAction n A := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [realAction_apply, Matrix.smul_mulVec, WithLp.toLp_smul,
    map_smul, smul_apply]

/-- A faithful real algebra homomorphism, with the ordinary matrix multiplication. -/
def realRepresentation (n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ →ₐ[ℝ]
      (Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)) where
  toFun := realAction n
  map_one' := realAction_one n
  map_mul' := realAction_mul n
  map_zero' := by
    apply ContinuousLinearMap.ext
    intro v
    simp [realAction_apply]
  map_add' := realAction_add n
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    rw [realAction_smul, realAction_one]

theorem inner_eq_re_pairing {N : Type*} [Fintype N] (u v : N → ℍ) :
    inner ℝ (WithLp.toLp 2 u : PiLp 2 (fun _ : N => ℍ)) (WithLp.toLp 2 v) =
      (pairing u v).re := by
  rw [PiLp.inner_apply]
  let reL : ℍ →ₗ[ℝ] ℝ := QuaternionAlgebra.reₗ _ _ _
  change (∑ i, inner ℝ (u i) (v i)) = reL (∑ i, star (u i) * v i)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change inner ℝ (u i) (v i) = (star (u i) * v i).re
  simp only [Quaternion.inner_def, Quaternion.re_mul, Quaternion.re_star,
    Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star]
  ring

theorem lpAction_inner (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ)
    (u v : QuaternionSpace n) :
    inner ℝ (lpAction n A u) v = inner ℝ u (lpAction n (star A) v) := by
  change inner ℝ (WithLp.toLp 2 (A *ᵥ WithLp.ofLp u) : QuaternionSpace n)
      (WithLp.toLp 2 (WithLp.ofLp v)) =
    inner ℝ (WithLp.toLp 2 (WithLp.ofLp u) : QuaternionSpace n)
      (WithLp.toLp 2 (star A *ᵥ WithLp.ofLp v))
  rw [inner_eq_re_pairing, inner_eq_re_pairing, pairing_mulVec_left]

/-- Quaternionic conjugate transpose is exactly the real Hilbert-space adjoint. -/
theorem realAction_star (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ) :
    realAction n (star A) = (realAction n A).adjoint := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro u v
  have he (x y : QuaternionSpace n) :
      inner ℝ (quaternionCoordinates n x) (quaternionCoordinates n y) = inner ℝ x y :=
    (quaternionCoordinates n).inner_map_map x y
  change inner ℝ
      (quaternionCoordinates n (lpAction n (star A) ((quaternionCoordinates n).symm u))) v =
    inner ℝ u (quaternionCoordinates n (lpAction n A ((quaternionCoordinates n).symm v)))
  conv_lhs => rhs; rw [← (quaternionCoordinates n).apply_symm_apply v]
  conv_rhs => lhs; rw [← (quaternionCoordinates n).apply_symm_apply u]
  rw [he, he, lpAction_inner, star_star]

/-- The standard quaternionic group embeds in the actual real orthogonal operator group. -/
def orthogonalRepresentation (n : ℕ) :
    SpGroup (Fin (n + 1)) →* OrthogonalOperators (4 * n + 4) where
  toFun A := ⟨⟨realAction n A.val,
    NoExoticSixSphere.OrthogonalCompactness.normPreserving_isInvertible _
      (realAction_norm n A)⟩, realAction_norm n A⟩
  map_one' := Subtype.ext (Subtype.ext (realAction_one n))
  map_mul' A B := Subtype.ext (Subtype.ext (realAction_mul n A.val B.val))

theorem continuous_orthogonalRepresentation (n : ℕ) : Continuous (orthogonalRepresentation n) :=
  (((continuous_realAction n).comp continuous_subtype_val).subtype_mk _).subtype_mk _

theorem orthogonalRepresentation_injective (n : ℕ) :
    Function.Injective (orthogonalRepresentation n) := by
  intro A B h
  exact Subtype.ext (realAction_injective n
    (congrArg (fun C : OrthogonalOperators (4 * n + 4) => C.val.val) h))

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns
