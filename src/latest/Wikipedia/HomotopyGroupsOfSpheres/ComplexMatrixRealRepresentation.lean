import Wikipedia.HomotopyGroupsOfSpheres.ImaginarySymmetricMatrices
import Wikipedia.NoExoticSixSphere.OrthogonalCompactness
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# The faithful real action of complex matrices

Complex matrices act on their ordinary complex Euclidean vector space.
Real orthonormal coordinates turn this into a real operator representation,
preserving multiplication and adjoints. Unitary matrices therefore give
actual real orthogonal operators.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexMatrixRealRepresentation

open NoExoticSixSphere.GLOrthonormalization

variable {N : Type*} [Fintype N] [DecidableEq N]

abbrev ComplexSpace (N : Type*) [Fintype N] := EuclideanSpace ℂ N
abbrev RealSpace (N : Type*) [Fintype N] := EuclideanSpace ℝ (Fin (2 * Fintype.card N))

omit [DecidableEq N] in
theorem complexSpace_finrank : Module.finrank ℝ (ComplexSpace N) = 2 * Fintype.card N := by
  rw [(WithLp.linearEquiv 2 ℝ (N → ℂ)).finrank_eq, Module.finrank_pi_fintype]
  simp [Complex.finrank_real_complex, Nat.mul_comm]

def coordinates (N : Type*) [Fintype N] : ComplexSpace N ≃ₗᵢ[ℝ] RealSpace N :=
  ((stdOrthonormalBasis ℝ (ComplexSpace N)).reindex (finCongr complexSpace_finrank)).repr

def action (A : Matrix N N ℂ) : RealSpace N →L[ℝ] RealSpace N :=
  (coordinates N).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((((Matrix.toEuclideanCLM (n := N) (𝕜 := ℂ)) A).restrictScalars ℝ).comp
      (coordinates N).symm.toContinuousLinearEquiv.toContinuousLinearMap)

theorem action_apply (A : Matrix N N ℂ) (v : RealSpace N) :
    action A v = coordinates N
      (Matrix.toEuclideanCLM (n := N) (𝕜 := ℂ) A ((coordinates N).symm v)) := rfl

theorem action_one : action (1 : Matrix N N ℂ) = 1 := by
  apply ContinuousLinearMap.ext
  intro v
  rw [action_apply, map_one]
  exact (coordinates N).apply_symm_apply v

theorem action_mul (A B : Matrix N N ℂ) : action (A * B) = action A * action B := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [action_apply, map_mul, mul_apply_eq_comp,
    (coordinates N).symm_apply_apply]

theorem action_add (A B : Matrix N N ℂ) : action (A + B) = action A + action B := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [action_apply, map_add, add_apply]

theorem action_smul (c : ℝ) (A : Matrix N N ℂ) : action (c • A) = c • action A := by
  apply ContinuousLinearMap.ext
  intro v
  have hs : Matrix.toEuclideanCLM (n := N) (𝕜 := ℂ) (c • A) =
      c • Matrix.toEuclideanCLM (n := N) (𝕜 := ℂ) A :=
    ((Matrix.toEuclideanCLM (n := N) (𝕜 := ℂ)).toAlgEquiv.toLinearEquiv.restrictScalars ℝ)
      |>.map_smul c A
  simp only [action_apply, hs, smul_apply, map_smul]

def representation : Matrix N N ℂ →ₐ[ℝ] (RealSpace N →L[ℝ] RealSpace N) where
  toFun := action
  map_one' := action_one
  map_mul' := action_mul
  map_zero' := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [action_apply, map_zero, zero_apply]
  map_add' := action_add
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, action_smul, action_one]

theorem action_injective : Function.Injective (action : Matrix N N ℂ → _) := by
  intro A B h
  apply (Matrix.toEuclideanCLM (n := N) (𝕜 := ℂ)).injective
  apply ContinuousLinearMap.ext
  intro u
  apply (coordinates N).injective
  have he := congrArg (fun L : RealSpace N →L[ℝ] RealSpace N ↦ L (coordinates N u)) h
  simpa only [action_apply, (coordinates N).symm_apply_apply] using! he

theorem continuous_action : Continuous (action : Matrix N N ℂ → _) :=
  representation.toLinearMap.continuous_of_finiteDimensional

omit [DecidableEq N] in
theorem real_inner_eq_complex (u v : ComplexSpace N) : inner ℝ u v = (inner ℂ u v).re := by
  rw [PiLp.inner_apply, PiLp.inner_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro a _
  rfl

theorem action_star (A : Matrix N N ℂ) : action (star A) = (action A).adjoint := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro u v
  have he (x y : ComplexSpace N) :
      inner ℝ (coordinates N x) (coordinates N y) = inner ℝ x y :=
    (coordinates N).inner_map_map x y
  change inner ℝ (coordinates N
      (Matrix.toEuclideanCLM (n := N) (𝕜 := ℂ) (star A) ((coordinates N).symm u))) v =
    inner ℝ u (coordinates N
      (Matrix.toEuclideanCLM (n := N) (𝕜 := ℂ) A ((coordinates N).symm v)))
  conv_lhs => rhs; rw [← (coordinates N).apply_symm_apply v]
  conv_rhs => lhs; rw [← (coordinates N).apply_symm_apply u]
  rw [he, he, real_inner_eq_complex, real_inner_eq_complex, map_star]
  exact congrArg Complex.re (ContinuousLinearMap.adjoint_inner_left _ _ _)

theorem action_unitary_norm (U : unitary (Matrix N N ℂ)) (v : RealSpace N) :
    ‖action U.val v‖ = ‖v‖ := by
  have hU : (action U.val).adjoint * action U.val = 1 := by
    rw [← action_star, ← action_mul, Unitary.star_mul_self_of_mem U.property, action_one]
  have hsq : ‖action U.val v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← ContinuousLinearMap.adjoint_inner_left]
    change inner ℝ (((action U.val).adjoint * action U.val) v) v = ‖v‖ ^ 2
    rw [hU]
    exact real_inner_self_eq_norm_sq v
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

def orthogonal : unitary (Matrix N N ℂ) →* OrthogonalOperators (2 * Fintype.card N) where
  toFun U := ⟨⟨action U.val,
    NoExoticSixSphere.OrthogonalCompactness.normPreserving_isInvertible _
      (action_unitary_norm U)⟩, action_unitary_norm U⟩
  map_one' := Subtype.ext (Subtype.ext action_one)
  map_mul' U V := Subtype.ext (Subtype.ext (action_mul U.val V.val))

theorem continuous_orthogonal : Continuous (orthogonal (N := N)) :=
  (((continuous_action (N := N)).comp continuous_subtype_val).subtype_mk _).subtype_mk _

theorem orthogonal_injective : Function.Injective (orthogonal (N := N)) := by
  intro U V h
  apply Subtype.ext
  exact action_injective
    (congrArg (fun B : OrthogonalOperators (2 * Fintype.card N) ↦ B.val.val) h)

end Wikipedia.HomotopyGroupsOfSpheres.ComplexMatrixRealRepresentation
