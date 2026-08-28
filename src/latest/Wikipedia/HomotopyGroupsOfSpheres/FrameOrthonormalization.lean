import Wikipedia.NoExoticSixSphere.RectangularOrthonormalization

/-!
# Rectangular orthonormalization fixes frames

The continuous Gram--Schmidt construction is the identity on an already
orthonormal frame. This supplies the stationary condition for local transport.
-/

noncomputable section

namespace NoExoticSixSphere.Stiefel.Orthonormalization

open GLOrthonormalization InnerProductSpace

variable {X : Type*} {N n : ℕ}

theorem normalized_eq_of_frame (A : X → Vector n →L[ℝ] Vector N)
    (x : X) (B : Space N n) (h : A x = B.val) (i : Fin n) :
    normalized A x i = columns A x i := by
  have ho : Orthonormal ℝ (columns A x) := by
    change Orthonormal ℝ (fun i ↦ A x (EuclideanSpace.basisFun (Fin n) ℝ i))
    rw [h]
    exact (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.comp_linearIsometry (toIsometry B)
  rw [normalized, gramSchmidtNormed, gramSchmidt_of_orthogonal ℝ ho.2, ho.1 i]
  simp

theorem frame_eq_of_frame (A : X → Vector n →L[ℝ] Vector N)
    (hi : ∀ x, Function.Injective (A x)) (x : X) (B : Space N n)
    (h : A x = B.val) : frame A hi x = B := by
  have hl : linearMap A x = B.val.toLinearMap := by
    apply (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ext
    intro i
    change linearMap A x (EuclideanSpace.basisFun (Fin n) ℝ i) =
      B.val (EuclideanSpace.basisFun (Fin n) ℝ i)
    rw [linearMap_basis, normalized_eq_of_frame A x B h]
    exact congrArg (fun T : Vector n →L[ℝ] Vector N ↦
      T (EuclideanSpace.basisFun (Fin n) ℝ i)) h
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro v
  exact congrArg (fun T : Vector n →ₗ[ℝ] Vector N ↦ T v) hl

end NoExoticSixSphere.Stiefel.Orthonormalization
