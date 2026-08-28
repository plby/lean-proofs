import Wikipedia.NoExoticSixSphere.PartialFrames
import Wikipedia.NoExoticSixSphere.ContinuousGramSchmidt

/-!
# Continuous orthonormalization of rectangular injective operators

Gram--Schmidt preserves the actual range. Its normalized independent columns
define an isometric embedding from the original Euclidean coordinate space,
continuously in operator norm. No square or surjective operator is required.
-/

noncomputable section

open Set InnerProductSpace Module

namespace NoExoticSixSphere.Stiefel.Orthonormalization

open GLOrthonormalization

variable {X : Type*} {N n : ℕ}
variable (A : X → Vector n →L[ℝ] Vector N) (hi : ∀ x, Function.Injective (A x))

def columns (x : X) (i : Fin n) : Vector N := A x (EuclideanSpace.basisFun (Fin n) ℝ i)

include hi in
theorem columns_independent (x : X) : LinearIndependent ℝ (columns A x) :=
  (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.linearIndependent.map'
    (A x).toLinearMap (LinearMap.ker_eq_bot.mpr (hi x))

def normalized (x : X) : Fin n → Vector N := gramSchmidtNormed ℝ (columns A x)

include hi in
theorem normalized_orthonormal (x : X) : Orthonormal ℝ (normalized A x) :=
  gramSchmidtNormed_orthonormal (columns_independent A hi x)

def linearMap (x : X) : Vector n →ₗ[ℝ] Vector N :=
  (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.constr ℝ (normalized A x)

theorem linearMap_basis (x : X) (i : Fin n) :
    linearMap A x (EuclideanSpace.basisFun (Fin n) ℝ i) = normalized A x i :=
  (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.constr_basis ℝ (normalized A x) i

include hi in
theorem linearMap_orthonormal (x : X) :
    Orthonormal ℝ ((linearMap A x) ∘ (EuclideanSpace.basisFun (Fin n) ℝ).toBasis) := by
  have he : (linearMap A x) ∘ (EuclideanSpace.basisFun (Fin n) ℝ).toBasis =
      normalized A x := funext (linearMap_basis A x)
  rw [he]
  exact normalized_orthonormal A hi x

def frame (x : X) : Space N n :=
  ofIsometry ((linearMap A x).isometryOfOrthonormal
    (v := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis)
    (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal (linearMap_orthonormal A hi x))

theorem frame_range (x : X) : (frame A hi x).val.range = (A x).range := by
  change (linearMap A x).range = (A x).toLinearMap.range
  rw [linearMap, Basis.constr_range, normalized,
    span_gramSchmidtNormed_range, span_gramSchmidt]
  have he : (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.constr ℝ (columns A x) =
      (A x).toLinearMap :=
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.constr_eq ℝ (fun _ ↦ rfl)
  rw [← he, Basis.constr_range]

variable [TopologicalSpace X]

theorem continuous_frame (hA : Continuous A) : Continuous (frame A hi) := by
  have hc (i : Fin n) : Continuous (fun x ↦ columns A x i) :=
    hA.clm_apply continuous_const
  have hn (i : Fin n) : Continuous (fun x ↦ normalized A x i) :=
    continuous_gramSchmidtNormed (columns A) hc (columns_independent A hi) i
  have hf : Continuous (fun x ↦ (frame A hi x).val) := by
    apply continuous_clm_apply.mpr
    intro w
    have he : (fun x ↦ (frame A hi x).val w) =
        fun x ↦ ∑ i, (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.equivFun w i •
          normalized A x i := by
      funext x
      exact (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.constr_apply_fintype ℝ
        (normalized A x) w
    rw [he]
    apply continuous_finsetSum
    intro i _
    exact (continuous_const : Continuous (fun _ : X ↦
      ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis.equivFun w i : ℝ))).smul (hn i)
  exact hf.subtype_mk _

def map (hA : Continuous A) : C(X, Space N n) := ⟨frame A hi, continuous_frame A hi hA⟩

end NoExoticSixSphere.Stiefel.Orthonormalization
