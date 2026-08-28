import Wikipedia.NoExoticSixSphere.RectangularOrthonormalization
import Wikipedia.NoExoticSixSphere.SmoothGramSchmidt

/-!
# Smooth normalization of rectangular operators, fixing actual isometries

The ambient normalized operator is defined everywhere. It is smooth at each
injective input, preserves its actual range, and fixes norm-preserving
operators exactly. Thus relative approximation need not alter protected frames.
-/

noncomputable section

open InnerProductSpace Module
open scoped ContDiff

namespace NoExoticSixSphere.Stiefel.Orthonormalization

open GLOrthonormalization

variable {X : Type*} {N n : ℕ}

def operator (A : X → Vector n →L[ℝ] Vector N) (x : X) : Vector n →L[ℝ] Vector N :=
  (linearMap A x).toContinuousLinearMap

theorem operator_eq_frame (A : X → Vector n →L[ℝ] Vector N)
    (hi : ∀ x, Function.Injective (A x)) (x : X) : operator A x = (frame A hi x).val := rfl

def coordinate (n : ℕ) (i : Fin n) : Vector n →L[ℝ] ℝ :=
  ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis.coord i).toContinuousLinearMap

theorem operator_eq_sum (A : X → Vector n →L[ℝ] Vector N) (x : X) :
    operator A x = ∑ i, (coordinate n i).smulRight (normalized A x i) := by
  apply ContinuousLinearMap.ext
  intro w
  change linearMap A x w = _
  rw [linearMap, Basis.constr_apply_fintype]
  simp only [sum_apply, ContinuousLinearMap.smulRight_apply]
  rfl

theorem operator_range (A : X → Vector n →L[ℝ] Vector N) (x : X)
    (hi : Function.Injective (A x)) : (operator A x).range = (A x).range := by
  let B : Unit → Vector n →L[ℝ] Vector N := fun _ ↦ A x
  exact frame_range B (fun _ ↦ hi) ()

theorem operator_norm (A : X → Vector n →L[ℝ] Vector N) (x : X)
    (hi : Function.Injective (A x)) (w : Vector n) : ‖operator A x w‖ = ‖w‖ := by
  let B : Unit → Vector n →L[ℝ] Vector N := fun _ ↦ A x
  exact (frame B (fun _ ↦ hi) ()).property w

theorem operator_eq_self (A : X → Vector n →L[ℝ] Vector N) (x : X)
    (hi : ∀ w, ‖A x w‖ = ‖w‖) : operator A x = A x := by
  let T : Vector n →ₗᵢ[ℝ] Vector N := toIsometry ⟨A x, hi⟩
  have ho : Orthonormal ℝ (columns A x) :=
    (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.comp_linearIsometry T
  have hn (i : Fin n) : normalized A x i = columns A x i := by
    change ‖gramSchmidt ℝ (columns A x) i‖⁻¹ • gramSchmidt ℝ (columns A x) i = _
    rw [gramSchmidt_of_orthogonal ℝ ho.2, ho.1 i, inv_one, one_smul]
  have he : (operator A x).toLinearMap = (A x).toLinearMap := by
    apply (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ext
    intro i
    change linearMap A x (EuclideanSpace.basisFun (Fin n) ℝ i) = A x _
    rw [linearMap_basis, hn]
    rfl
  exact ContinuousLinearMap.ext (fun w ↦ congrArg (fun L : Vector n →ₗ[ℝ] Vector N ↦ L w) he)

variable [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem contDiffAt_operator (A : X → Vector n →L[ℝ] Vector N) (x : X)
    (hA : ContDiffAt ℝ ∞ A x) (hi : Function.Injective (A x)) :
    ContDiffAt ℝ ∞ (operator A) x := by
  have hc (i : Fin n) : ContDiffAt ℝ ∞ (fun y ↦ columns A y i) x :=
    hA.clm_apply contDiffAt_const
  have hli : LinearIndependent ℝ (columns A x) :=
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.linearIndependent.map'
      (A x).toLinearMap (LinearMap.ker_eq_bot.mpr hi)
  have hn (i : Fin n) : ContDiffAt ℝ ∞ (fun y ↦ normalized A y i) x :=
    contDiffAt_gramSchmidtNormed (columns A) hc hli i
  have he : operator A = fun y ↦ ∑ i, (coordinate n i).smulRight (normalized A y i) :=
    funext (operator_eq_sum A)
  rw [he]
  apply ContDiffAt.sum
  intro i _
  exact contDiffAt_const.smulRight (hn i)

end NoExoticSixSphere.Stiefel.Orthonormalization
